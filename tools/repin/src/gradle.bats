(* gradle -- the Gradle wrapper move of repin (bats-lang/repository-prototype#413).
   Keyword: repin gradle.

   Three texts decide the move of a gradle-wrapper.properties; none is a network call, and
   no YAML is read:

   - the properties text, read by line: `distributionUrl` must be exactly
     `distributionUrl=https\://services.gradle.org/distributions/gradle-<version>-bin.zip`
     with <version> a plain version tag (version.bats), and `distributionSha256Sum`, when
     there, `distributionSha256Sum=` and 64 lowercase hex digits; each at most once, at the
     start of its line. A line of either key in any other spelling (a blank before it, a
     `-all.zip`, a url of another host, a CR before the newline) is refused, named by its
     number, and nothing is decided. A comment (`#` or `!`) and the other keys are skipped.
   - the versions text, the body of https://services.gradle.org/versions/all: a JSON array
     of objects with the strings `version`, `buildTime` (`yyyyMMddHHmmss` and a sign and
     `hhmm`, a zone offset) and `rcFor` and the booleans `snapshot` and `nightly`. A release
     is stable when it is no snapshot, no nightly, has no `rcFor` and its version is a plain
     version tag. A stable release's `buildTime` is its published time, in seconds since the
     epoch.
   - the checksum text, the body of the target's `gradle-<version>-bin.zip.sha256`: 64
     lowercase hex digits and, at most, one newline. It is read only when the pin moves, and
     is then copied as it is, never computed.

   The target is the highest stable release of the major of the wrapper's version that is
   higher than it and a candidate (at least 7 days old at now, age.bats): the pin is `moved`
   to it. When there is none but there are younger ones, the newest of them is `too new`. The
   highest stable release of a higher major, of any age, is its own row, `major, not moved`,
   never a target, beside the row of the candidates when there is one. A wrapper with none of
   these rows is `current`, and its version must be a stable release of the versions. Each row
   is a move record (records.bats) of the kind `gradle`, the name `gradle`, with the age of the
   release the row names. A text that is not as said is an error and nothing is decided. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use json as J
#use result as R

staload "age.sats"
staload "records.sats"
staload "support.sats"
staload "version.sats"

(* ============================================================
   The properties text
   ============================================================ *)

fn _text_length {literal_len:nat} (literal: string literal_len): int literal_len =
  g1u2i(string1_length(literal))

fun _hex_run {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if (value >= 48 && value <= 57) || (value >= 97 && value <= 102) then
      _hex_run(bytes, i + 1, j)
    else false
  end

(* The first place of bytes[i, limit) that is not a space or a tab, or limit *)
fun _skip_blank {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i): [k:nat | i <= k; k <= limit] int k =
  if i >= limit then i
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if value = 32 || value = 9 then _skip_blank(bytes, limit, i + 1) else i
  end

(* The end of a key: the first '=', ':', space or tab, as a properties file ends it *)
fun _key_end {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i): [k:nat | i <= k; k <= limit] int k =
  if i >= limit then i
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if value = 61 || value = 58 || value = 32 || value = 9 then i
    else _key_end(bytes, limit, i + 1)
  end

(* Whether bytes[start, stop) begins with the literal *)
fn _prefix_is {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}{literal_len:nat}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop,
   literal: string literal_len): bool =
  if stop - start < _text_length(literal) then false
  else span_is(bytes, start, start + _text_length(literal), literal)

(* The line bytes[start, stop) as a distributionUrl line: whether it is exactly the one
   spelling, and where its version is *)
fn _url_value {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [vs,ve:nat | vs <= ve; ve <= stop] @(bool, int vs, int ve) = let
  val prefix_len =
    _text_length("distributionUrl=https\\://services.gradle.org/distributions/gradle-")
in
  if stop - start < prefix_len + 9 then @(false, stop, stop)
  else if ~_prefix_is(bytes, start, stop,
    "distributionUrl=https\\://services.gradle.org/distributions/gradle-") then @(false, stop, stop)
  else if ~span_is(bytes, stop - 8, stop, "-bin.zip") then @(false, stop, stop)
  else if ~version_ok(bytes, start + prefix_len, stop - 8) then @(false, stop, stop)
  else @(true, start + prefix_len, stop - 8)
end

(* Whether the line bytes[start, stop) is exactly `distributionSha256Sum=` and 64 lowercase
   hex digits *)
fn _sha_line_ok {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool = let
  val prefix_len = _text_length("distributionSha256Sum=")
in
  if stop - start <> prefix_len + 64 then false
  else if ~_prefix_is(bytes, start, stop, "distributionSha256Sum=") then false
  else _hex_run(bytes, start + prefix_len, stop)
end

(* What the line bytes[start, stop) is: 0 a line to skip, 1 the distributionUrl line, 2 the
   distributionSha256Sum line, 3 a line of one of those two keys in a spelling that is
   refused. For 1 the version is bytes[vs, ve). *)
fn _classify {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [vs,ve:nat | vs <= ve; ve <= stop] @(int, int vs, int ve) = let
  val first = _skip_blank(bytes, stop, start)
in
  if first >= stop then @(0, stop, stop)
  else let
    val head = byte2int0($A.read<byte>(bytes, first))
  in
    if head = 35 || head = 33 then @(0, stop, stop)
    else let
      val key_stop = _key_end(bytes, stop, first)
    in
      if span_is(bytes, first, key_stop, "distributionUrl") then
        (if first <> start then @(3, stop, stop)
         else let
           val @(ok, vs, ve) = _url_value(bytes, start, stop)
         in if ok then @(1, vs, ve) else @(3, stop, stop) end)
      else if span_is(bytes, first, key_stop, "distributionSha256Sum") then
        (if first = start && _sha_line_ok(bytes, start, stop) then @(2, stop, stop)
         else @(3, stop, stop))
      else @(0, stop, stop)
    end
  end
end

fun _scan {l:agz}{n:pos}{len:nat | len <= n}{i:nat | i <= len}{number:pos}
  {url_start,url_stop:nat | url_start <= url_stop; url_stop <= len} .<len - i>.
  (bytes: !$A.borrow(byte, l, n), len: int len, i: int i, number: int number,
   url_start: int url_start, url_stop: int url_stop, sha_seen: bool)
  : [bad:nat][vs,ve:nat | vs <= ve; ve <= len] @(int bad, int vs, int ve) =
  if i >= len then @(0, url_start, url_stop)
  else let
    val stop = find_byte(bytes, len, i, 10)
    val @(kind, vs, ve) = _classify(bytes, i, stop)
  in
    if kind = 3 then @(number, url_start, url_stop)
    else if kind = 1 then
      (if url_stop > url_start then @(number, url_start, url_stop)
       else if stop >= len then @(0, vs, ve)
       else _scan(bytes, len, stop + 1, number + 1, vs, ve, sha_seen))
    else if kind = 2 then
      (if sha_seen then @(number, url_start, url_stop)
       else if stop >= len then @(0, url_start, url_stop)
       else _scan(bytes, len, stop + 1, number + 1, url_start, url_stop, true))
    else if stop >= len then @(0, url_start, url_stop)
    else _scan(bytes, len, stop + 1, number + 1, url_start, url_stop, sha_seen)
  end

(* The properties text[0, len): the number (from 1) of the first line that is one of the two
   keys in a spelling that is refused, or of a second line of a key, else 0; and the place of
   the version of the distributionUrl line, which is empty (vs = ve) when the text has no such
   line *)
#pub fn scan_properties {l:agz}{n:pos}{len:nat | len <= n}
  (text: !$A.borrow(byte, l, n), len: int len)
  : [bad:nat][vs,ve:nat | vs <= ve; ve <= len] @(int bad, int vs, int ve)

implement scan_properties (text, len) = _scan(text, len, 0, 1, 0, 0, false)

(* ============================================================
   The published time
   ============================================================ *)

fun _digits_only {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if value >= 48 && value <= 57 then _digits_only(bytes, i + 1, j) else false
  end

fun _digits_int {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j, value: int): int =
  if i >= j then value
  else _digits_int(bytes, i + 1, j, value * 10 + byte2int0($A.read<byte>(bytes, i)) - 48)

(* The days from 1970-01-01 to the civil date (year from 1970, month 1 to 12, day 1 to 31):
   the proleptic Gregorian calendar by eras of 400 years *)
fn _days_from_civil (year: int, month: int, day: int): lint = let
  val shifted_year = (if month <= 2 then year - 1 else year): int
  val era = shifted_year / 400
  val year_of_era = shifted_year - era * 400
  val shifted_month = (if month > 2 then month - 3 else month + 9): int
  val day_of_year = (153 * shifted_month + 2) / 5 + day - 1
  val day_of_era = year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year
in
  g0int2int_int_lint(era) * 146097L + g0int2int_int_lint(day_of_era) - 719468L
end

(* The seconds since the epoch of the Gradle build time bytes[start, stop): whether it is
   `yyyyMMddHHmmss` and a sign and `hhmm` (19 bytes, a valid date from 1970, a zone offset
   up to 23:59), and the time in UTC *)
#pub fn build_seconds {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (text: !$A.borrow(byte, l, n), start: int start, stop: int stop): @(bool, lint)

implement build_seconds (text, start, stop) =
  if stop - start <> 19 then @(false, 0L)
  else if ~_digits_only(text, start, start + 14) then @(false, 0L)
  else if ~_digits_only(text, start + 15, stop) then @(false, 0L)
  else let
    val sign = byte2int0($A.read<byte>(text, start + 14))
    val year = _digits_int(text, start, start + 4, 0)
    val month = _digits_int(text, start + 4, start + 6, 0)
    val day = _digits_int(text, start + 6, start + 8, 0)
    val hour = _digits_int(text, start + 8, start + 10, 0)
    val minute = _digits_int(text, start + 10, start + 12, 0)
    val second = _digits_int(text, start + 12, start + 14, 0)
    val offset_hour = _digits_int(text, start + 15, start + 17, 0)
    val offset_minute = _digits_int(text, start + 17, start + 19, 0)
  in
    if sign <> 43 && sign <> 45 then @(false, 0L)
    else if year < 1970 || month < 1 || month > 12 || day < 1 || day > 31 then @(false, 0L)
    else if hour > 23 || minute > 59 || second > 59 then @(false, 0L)
    else if offset_hour > 23 || offset_minute > 59 then @(false, 0L)
    else let
      val local_seconds = _days_from_civil(year, month, day) * 86400L
        + g0int2int_int_lint(hour * 3600 + minute * 60 + second)
      val offset = g0int2int_int_lint(offset_hour * 3600 + offset_minute * 60)
      val utc = (if sign = 43 then local_seconds - offset else local_seconds + offset): lint
    in
      if utc < 0L then @(false, 0L) else @(true, utc)
    end
  end

(* ============================================================
   The stable releases of the versions text
   ============================================================ *)

fun _copy_loop {l:agz}{cap:pos}{dlen:nat | dlen <= cap; dlen <= 4096}{i:nat | i <= dlen}
  {used:nat | used + (dlen - i) <= 524288} .<dlen - i>.
  (text: !$A.arr(byte, l, cap), dlen: int dlen, i: int i,
   out: !$B.builder(used) >> $B.builder(used + (dlen - i))): void =
  if i >= dlen then ()
  else let
    val () = $B.put_char(out, $AR.low_byte(byte2int0($A.get<byte>(text, i))))
  in _copy_loop(text, dlen, i + 1, out) end

(* The bytes of a JSON string appended to the empty builder: whether it fits (at most 4096
   bytes; a longer string is left out) *)
fn _copy_string {l:agz}{cap:pos}{dlen:nat | dlen <= cap}
  (text: !$A.arr(byte, l, cap), dlen: int dlen, out: !$B.builder(0) >> $B.builder_v): bool =
  if dlen <= 4096 then let val () = _copy_loop(text, dlen, 0, out) in true end else false

fun _text_is {l:agz}{cap:pos}{dlen:nat | dlen <= cap}{literal_len:nat | dlen == literal_len}
  {i:nat | i <= dlen} .<dlen - i>.
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len, i: int i): bool =
  if i >= dlen then true
  else if byte2int0($A.get<byte>(text, i)) = char2int0(string_get_at(literal, i)) then
    _text_is(text, dlen, literal, i + 1)
  else false

(* Whether the string text[0, dlen) is exactly the literal *)
fn _string_is {l:agz}{cap:pos}{dlen:nat | dlen <= cap}{literal_len:nat}
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len): bool =
  if dlen = _text_length(literal) then _text_is(text, dlen, literal, 0) else false

(* The string value of the field key of the object fields, copied to the empty builder out:
   whether the object has such a field with a string that fits. The first field of the name
   counts. *)
fun _find_field {fields_size:nat}{key_len:nat} .<fields_size>.
  (fields: !$J.json_entries(fields_size), key: string key_len,
   out: !$B.builder(0) >> $B.builder_v): bool =
  case+ fields of
  | $J.json_entries_nil() => false
  | $J.json_entries_cons(field_key, field_key_len, value, rest) =>
    if _string_is(field_key, field_key_len, key) then
      (case+ value of
       | $J.json_str(text, text_len) => let
           val copied = _copy_string(text, text_len, out)
         in copied end
       | _ => false)
    else _find_field(rest, key, out)

(* The boolean value of the field key of the object fields: 0 when the object has no such
   field with a boolean, 1 false, 2 true *)
fun _find_flag {fields_size:nat}{key_len:nat} .<fields_size>.
  (fields: !$J.json_entries(fields_size), key: string key_len): int =
  case+ fields of
  | $J.json_entries_nil() => 0
  | $J.json_entries_cons(field_key, field_key_len, value, rest) =>
    if _string_is(field_key, field_key_len, key) then
      (case+ value of
       | $J.json_bool(flag) => if flag then 2 else 1
       | _ => 0)
    else _find_flag(rest, key)

(* The line `<version> <build time>` and a newline appended to out, which has room *)
fn _append_line {version_loc,time_loc:agz}{version_size:pos}{time_size:pos | 19 <= time_size}
  {version_len:nat | version_len <= version_size}{used:nat | used + version_len + 21 <= 524288}
  (version: !$A.borrow(byte, version_loc, version_size), version_len: int version_len,
   time: !$A.borrow(byte, time_loc, time_size), out: !$B.builder(used) >> $B.builder_v): void = let
  val () = put_range(version, 0, version_len, out)
  val () = $B.put_char(out, $AR.low_byte(32))
  val () = put_range(time, 0, 19, out)
  val () = $B.put_char(out, $AR.low_byte(10))
in () end

(* The version and the build time of a stable release appended to out when the build time is
   valid and the line fits: 0 when it went well, else 1 (said on standard error) *)
fn _append_checked {version_loc,time_loc:agz}{version_size,time_size:pos}
  {version_len:nat | version_len <= version_size}{time_len:nat | time_len <= time_size}
  {used:nat | used <= 524288}
  (version: !$A.borrow(byte, version_loc, version_size), version_len: int version_len,
   time: !$A.borrow(byte, time_loc, time_size), time_len: int time_len, time_ok: bool,
   out: !$B.builder(used) >> $B.builder_v): int =
  if ~time_ok then let
    val () = prerrln! ("repin: a stable release of the versions has no buildTime")
  in 1 end
  else if time_len <> 19 then let
    val () = prerrln! ("repin: a stable release of the versions has no buildTime")
  in 1 end
  else if $B.length(out) + version_len + 21 > 524288 then let
    val () = prerrln! ("repin: the stable releases of the versions do not fit 524288 bytes")
  in 1 end
  else let
    val () = _append_line(version, version_len, time, out)
  in 0 end

(* A stable release: its build time read from the fields and the line appended *)
fn _stable_line {fields_size:nat}{version_loc:agz}{version_size:pos}
  {version_len:nat | version_len <= version_size}{used:nat | used <= 524288}
  (fields: !$J.json_entries(fields_size),
   version: !$A.borrow(byte, version_loc, version_size), version_len: int version_len,
   out: !$B.builder(used) >> $B.builder_v): int = let
  var time_builder : $B.builder(0) = $B.create()
  val time_found = _find_field(fields, "buildTime", time_builder)
  val @(time_array, time_len) = $B.to_arr(time_builder)
  val @(time_frozen, time_view) = $A.freeze<byte>(time_array)
  val time_pair =
    (if time_found then build_seconds(time_view, 0, time_len) else @(false, 0L)): @(bool, lint)
  val status = _append_checked(version, version_len, time_view, time_len, time_pair.0, out)
  val () = $A.drop<byte>(time_frozen, time_view)
  val () = $A.free<byte>($A.thaw<byte>(time_frozen))
in status end

(* What a release is, by its facts: the version, whether the fields rcFor, snapshot and
   nightly were there, and their values *)
fn _release_checked {fields_size:nat}{version_loc:agz}{version_size:pos}
  {version_len:nat | version_len <= version_size}{used:nat | used <= 524288}
  (fields: !$J.json_entries(fields_size),
   version: !$A.borrow(byte, version_loc, version_size), version_len: int version_len,
   candidate_found: bool, candidate_len: int, snapshot: int, nightly: int,
   out: !$B.builder(used) >> $B.builder_v): int =
  if version_len <= 0 then let
    val () = prerrln! ("repin: a release of the versions has no version")
  in 1 end
  else if ~candidate_found then let
    val () = prerrln! ("repin: a release of the versions has no rcFor")
  in 1 end
  else if snapshot = 0 then let
    val () = prerrln! ("repin: a release of the versions has no snapshot")
  in 1 end
  else if nightly = 0 then let
    val () = prerrln! ("repin: a release of the versions has no nightly")
  in 1 end
  else if snapshot = 2 then 0
  else if nightly = 2 then 0
  else if candidate_len > 0 then 0
  else if ~version_ok(version, 0, version_len) then 0
  else _stable_line(fields, version, version_len, out)

(* One release object appended to the lines text as `<version> <build time>` and a newline
   when it is stable, and nothing when it is not: 0 when it went well, else 1 (said on
   standard error). The lines text stays under 524288 bytes: a release that would not fit is an
   error. *)
fn _release_line {fields_size:nat}{used:nat | used <= 524288}
  (fields: !$J.json_entries(fields_size), out: !$B.builder(used) >> $B.builder_v): int = let
  var version_builder : $B.builder(0) = $B.create()
  val version_found = _find_field(fields, "version", version_builder)
  val @(version_array, version_len) = $B.to_arr(version_builder)
  val @(version_frozen, version_view) = $A.freeze<byte>(version_array)
  var candidate_builder : $B.builder(0) = $B.create()
  val candidate_found = _find_field(fields, "rcFor", candidate_builder)
  val @(candidate_array, candidate_len) = $B.to_arr(candidate_builder)
  val () = $A.free<byte>(candidate_array)
  val snapshot = _find_flag(fields, "snapshot")
  val nightly = _find_flag(fields, "nightly")
  val status = _release_checked(fields, version_view, version_len, candidate_found,
    candidate_len, snapshot, nightly, out)
  val () = $A.drop<byte>(version_frozen, version_view)
  val () = $A.free<byte>($A.thaw<byte>(version_frozen))
in
  if version_found then status else 1
end

(* Every release of the list, in order: 0 when all went well, else 1 *)
fun _collect {list_size:nat}{used:nat | used <= 524288} .<list_size>.
  (releases: !$J.json_list(list_size), out: !$B.builder(used) >> $B.builder_v): int =
  case+ releases of
  | $J.json_list_nil() => 0
  | $J.json_list_cons(release, rest) =>
    (case+ release of
     | $J.json_obj(fields) => let
         val failed = _release_line(fields, out)
       in
         if failed > 0 then 1 else _collect(rest, out)
       end
     | _ => let val () = prerrln! ("repin: a release of the versions is not an object") in 1 end)

(* ============================================================
   Choosing a release
   ============================================================ *)

fun _error_span {l:agz}{n:pos}{i,stop:nat | i <= stop; stop <= n} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, stop: int stop): void =
  if i >= stop then ()
  else let
    val () = prerr_char(int2char0(byte2int0($A.read<byte>(bytes, i))))
  in _error_span(bytes, i + 1, stop) end

(* bytes[start, stop) appended to out *)
fn _copy_span {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop, out: !$B.sized_rope): void =
  if stop > start then $B.sized_rope_copy(out, bytes, start, stop) else ()

(* Which release a scan looks for, among the lines `<version> <build time>`, for a wrapper
   of the version current:
   0 the highest version of current's major that is higher than it and a candidate at now,
   1 the highest version of current's major that is higher than it and not a candidate,
   2 the highest version of a major higher than current's,
   3 the release of current's own version *)
fn _matches {lines_loc,current_loc:agz}{lines_size,current_size:pos}
  {stop:nat | stop <= lines_size}{start:nat | start <= stop}
  {current_len:nat | current_len <= current_size}
  (lines: !$A.borrow(byte, lines_loc, lines_size), start: int start, stop: int stop,
   mode: int, current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   now: lint): bool = let
  val space = find_byte(lines, stop, start, 32)
in
  if space >= stop then false
  else if mode = 3 then spans_equal(lines, start, space, current, 0, current_len)
  else let
    val release_major = version_major(lines, start, space)
    val current_major = version_major(current, 0, current_len)
  in
    if mode = 2 then release_major > current_major
    else if release_major <> current_major then false
    else if version_compare(lines, start, space, current, 0, current_len) <= 0 then false
    else let
      val @(_, published) = build_seconds(lines, space + 1, stop)
    in
      if mode = 0 then is_candidate(now, published) else ~is_candidate(now, published)
    end
  end
end

(* Whether the version of the line lines[start, stop) is higher than the version of the line
   that starts at best. A borrow cannot be passed twice to one call, so the version of the
   best line is copied to compare with. *)
fn _higher {l:agz}{n:pos | n <= 524288}{lines_len:nat | lines_len <= n}
  {stop:nat | stop <= lines_len}{start:nat | start <= stop}{best:nat | best <= lines_len}
  (lines: !$A.borrow(byte, l, n), lines_len: int lines_len, start: int start,
   stop: int stop, best: int best): bool = let
  val best_stop = find_byte(lines, lines_len, best, 10)
  val space = find_byte(lines, stop, start, 32)
  val best_space = find_byte(lines, best_stop, best, 32)
  var copy : $B.builder(0) = $B.create()
  val () = put_range(lines, best, best_space, copy)
  val @(copy_array, copy_len) = $B.to_arr(copy)
  val @(copy_frozen, copy_view) = $A.freeze<byte>(copy_array)
  val higher = version_compare(lines, start, space, copy_view, 0, copy_len) > 0
  val () = $A.drop<byte>(copy_frozen, copy_view)
  val () = $A.free<byte>($A.thaw<byte>(copy_frozen))
in higher end

(* The line of the mode with the highest version (the first of equals): whether there is
   one, and where it starts *)
fun _best {lines_loc,current_loc:agz}{lines_size:pos | lines_size <= 524288}{current_size:pos}
  {lines_len:nat | lines_len <= lines_size}{i:nat | i <= lines_len}
  {best:nat | best <= lines_len}{current_len:nat | current_len <= current_size}
  .<lines_len - i>.
  (lines: !$A.borrow(byte, lines_loc, lines_size), lines_len: int lines_len, i: int i,
   mode: int, current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   now: lint, found: bool, best: int best)
  : [chosen:nat | chosen <= lines_len] @(bool, int chosen) =
  if i >= lines_len then @(found, best)
  else let
    val stop = find_byte(lines, lines_len, i, 10)
    val matched = _matches(lines, i, stop, mode, current, current_len, now)
    val take =
      (if ~matched then false
       else if found then _higher(lines, lines_len, i, stop, best)
       else true): bool
    val found2 = (if take then true else found): bool
    val best2 = (if take then i else best): [chosen:nat | chosen <= lines_len] int chosen
  in
    if stop >= lines_len then @(found2, best2)
    else _best(lines, lines_len, stop + 1, mode, current, current_len, now, found2, best2)
  end

(* The move record of the release on the line that starts at line: the wrapper's version,
   the release's, its age in days and the status *)
fn _put_row {lines_loc,current_loc:agz}{lines_size,current_size:pos}
  {lines_len:nat | lines_len <= lines_size}{line:nat | line <= lines_len}
  {current_len:nat | current_len <= current_size}
  (records: !$B.sized_rope, lines: !$A.borrow(byte, lines_loc, lines_size),
   lines_len: int lines_len, line: int line,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   now: lint, status: move_status): void = let
  val stop = find_byte(lines, lines_len, line, 10)
  val space = find_byte(lines, stop, line, 32)
  val published =
    (if space < stop then (build_seconds(lines, space + 1, stop)).1 else 0L): lint
  val () = $B.sized_rope_bput(records, "gradle\tgradle\t")
  val () = _copy_span(current, 0, current_len, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = _copy_span(lines, line, space, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_age(records, age_days(now, published))
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_status(records, status)
  val () = $B.sized_rope_bput(records, "\n")
in () end

(* The rows of the wrapper of the version current[0, current_len) among the stable releases
   lines[0, lines_len): 0 when nothing moves, 1 when it moves (the target's version and a
   newline are appended to updates), 2 when it fails (said on standard error) *)
fn _decide_lines {lines_loc,current_loc:agz}{lines_size:pos | lines_size <= 524288}{current_size:pos}
  {lines_len:nat | lines_len <= lines_size}{current_len:nat | current_len <= current_size}
  (lines: !$A.borrow(byte, lines_loc, lines_size), lines_len: int lines_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): int = let
  val @(moved_found, moved) = _best(lines, lines_len, 0, 0, current, current_len, now, false, 0)
  val @(young_found, young) = _best(lines, lines_len, 0, 1, current, current_len, now, false, 0)
  val @(major_found, major) = _best(lines, lines_len, 0, 2, current, current_len, now, false, 0)
in
  if moved_found then let
    val () = _put_row(records, lines, lines_len, moved, current, current_len, now, Status_moved())
    val stop = find_byte(lines, lines_len, moved, 10)
    val space = find_byte(lines, stop, moved, 32)
    val () = _copy_span(lines, moved, space, updates)
    val () = $B.sized_rope_bput(updates, "\n")
    val () =
      if major_found then
        _put_row(records, lines, lines_len, major, current, current_len, now,
          Status_major_not_moved())
      else ()
  in 1 end
  else if young_found then let
    val () = _put_row(records, lines, lines_len, young, current, current_len, now, Status_too_new())
    val () =
      if major_found then
        _put_row(records, lines, lines_len, major, current, current_len, now,
          Status_major_not_moved())
      else ()
  in 0 end
  else if major_found then let
    val () = _put_row(records, lines, lines_len, major, current, current_len, now,
      Status_major_not_moved())
  in 0 end
  else let
    val @(own_found, own) = _best(lines, lines_len, 0, 3, current, current_len, now, false, 0)
  in
    if own_found then let
      val () = _put_row(records, lines, lines_len, own, current, current_len, now,
        Status_current())
    in 0 end
    else let
      val () = prerr! ("repin: the versions have no stable release ")
      val () = _error_span(current, 0, current_len)
      val () = prerrln! ()
    in 2 end
  end
end

(* ============================================================
   The three texts
   ============================================================ *)

fun _copy_exact {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m <= capacity}
  {i:nat | i <= m} .<m - i>.
  (source: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity),
   i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(source, i))
  in _copy_exact(source, m, destination, i + 1) end

(* The JSON text text[0, len) parsed whole (the parser wants an array of exactly the text's
   size, so the text is copied to one): whether it is one value with nothing after it but
   blanks, and the value (null when it is not). The failure is said on standard error. *)
fn _parsed {l:agz}{len:nat | len <= 524288}
  (text: !$A.borrow(byte, l, 524288), len: int len): @(bool, $J.json_v) =
  if len <= 0 then let
    val () = prerrln! ("repin: the versions text is empty")
  in @(false, $J.json_null()) end
  else let
    val exact = $A.alloc<byte>(len)
    val () = _copy_exact(text, len, exact, 0)
    val @(frozen, view) = $A.freeze<byte>(exact)
    val parsed =
      (case+ $J.parse_text(view, len) of
       | ~$R.err(failure) => let
           val position = $J.parse_error_pos(failure)
           val () = prerrln! ("repin: the versions text is not JSON, at byte ", position)
         in @(false, $J.json_null()) end
       | ~$R.ok(root) => @(true, root)): @(bool, $J.json_v)
    val () = $A.drop<byte>(frozen, view)
    val () = $A.free<byte>($A.thaw<byte>(frozen))
  in parsed end

(* The checksum text checksum[0, len): 64 lowercase hex digits and at most one newline *)
fn _checksum_ok {l:agz}{n:pos}{len:nat | len <= n}
  (checksum: !$A.borrow(byte, l, n), len: int len): bool =
  if len = 64 then _hex_run(checksum, 0, len)
  else if len = 65 then
    (if byte2int0($A.read<byte>(checksum, 64)) <> 10 then false
     else _hex_run(checksum, 0, 64))
  else false

(* The line of the properties text that starts at the line number target, said as refused *)
fun _line_start {l:agz}{n:pos}{len:nat | len <= n}{i:nat | i <= len} .<len - i>.
  (text: !$A.borrow(byte, l, n), len: int len, i: int i, number: int, target: int)
  : [k:nat | k <= len] int k =
  if number >= target then i
  else let
    val stop = find_byte(text, len, i, 10)
  in
    if stop >= len then i else _line_start(text, len, stop + 1, number + 1, target)
  end

fn _say_refused {l:agz}{n:pos}{len:nat | len <= n}
  (text: !$A.borrow(byte, l, n), len: int len, number: int): void = let
  val start = _line_start(text, len, 0, 1, number)
  val stop = find_byte(text, len, start, 10)
  val () = prerr! ("repin: refused, not the one spelling of a Gradle wrapper pin: line ", number, ": ")
  val () = _error_span(text, start, stop)
  val () = prerrln! ()
in () end

(* The stable releases lines[0, lines_len) decide the move of the wrapper version current;
   the checksum text is copied to updates when the pin moves *)
fn _decide_with_lines {lines_loc,current_loc,checksum_loc:agz}{lines_size:pos | lines_size <= 524288}
  {current_size:pos}{lines_len:nat | lines_len <= lines_size}
  {current_len:nat | current_len <= current_size}{checksum_len:nat | checksum_len <= 524288}
  (lines: !$A.borrow(byte, lines_loc, lines_size), lines_len: int lines_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   checksum: !$A.borrow(byte, checksum_loc, 524288), checksum_len: int checksum_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): int = let
  val decided = _decide_lines(lines, lines_len, current, current_len, now, records, updates)
in
  if decided = 2 then 1
  else if decided = 0 then 0
  else if _checksum_ok(checksum, checksum_len) then let
    val () = _copy_span(checksum, 0, 64, updates)
    val () = $B.sized_rope_bput(updates, "\n")
  in 0 end
  else let
    val () = prerrln! ("repin: the checksum text is not 64 lowercase hex digits")
  in 1 end
end

fn _free_other {size:nat} (root: $J.json(size)): void = $J.json_free(root)

(* What becomes of the wrapper of the properties text properties[0, properties_len) by the
   versions text and the checksum text, at now (whole seconds): the rows appended to records
   and, when the pin moves, the lines `<version>` and `<sha256>` to updates. 0 when it went
   well, else 1 (said on standard error), and then what was appended is to be discarded. Each
   text is in a buffer of 524288 bytes. *)
#pub fn decide_gradle {properties_loc,versions_loc,checksum_loc:agz}
  {properties_len,versions_len,checksum_len:nat | properties_len <= 524288;
   versions_len <= 524288; checksum_len <= 524288}
  (properties: !$A.borrow(byte, properties_loc, 524288), properties_len: int properties_len,
   versions: !$A.borrow(byte, versions_loc, 524288), versions_len: int versions_len,
   checksum: !$A.borrow(byte, checksum_loc, 524288), checksum_len: int checksum_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): int

implement decide_gradle (properties, properties_len, versions, versions_len, checksum,
  checksum_len, now, records, updates) = let
  val @(bad, version_start, version_stop) = scan_properties(properties, properties_len)
in
  if bad > 0 then let
    val () = _say_refused(properties, properties_len, bad)
  in 1 end
  else if version_start >= version_stop then let
    val () = prerrln! ("repin: the properties have no distributionUrl line")
  in 1 end
  else let
    val @(parsed_ok, root) = _parsed(versions, versions_len)
  in
    if ~parsed_ok then let val () = _free_other(root) in 1 end
    else
      (case+ root of
       | ~$J.json_arr(releases) => let
           var lines_builder : $B.builder(0) = $B.create()
           val failed = _collect(releases, lines_builder)
           val () = $J.json_list_free(releases)
           val @(lines_array, lines_len) = $B.to_arr(lines_builder)
           val @(lines_frozen, lines_view) = $A.freeze<byte>(lines_array)
           var current_builder : $B.builder(0) = $B.create()
           val () = put_range(properties, version_start, version_stop, current_builder)
           val @(current_array, current_len) = $B.to_arr(current_builder)
           val @(current_frozen, current_view) = $A.freeze<byte>(current_array)
           val status =
             (if failed > 0 then 1
              else _decide_with_lines(lines_view, lines_len, current_view, current_len,
                checksum, checksum_len, now, records, updates)): int
           val () = $A.drop<byte>(current_frozen, current_view)
           val () = $A.free<byte>($A.thaw<byte>(current_frozen))
           val () = $A.drop<byte>(lines_frozen, lines_view)
           val () = $A.free<byte>($A.thaw<byte>(lines_frozen))
         in status end
       | other => let
           val () = prerrln! ("repin: the versions text is not an array")
           val () = _free_other(other)
         in 1 end)
  end
end
