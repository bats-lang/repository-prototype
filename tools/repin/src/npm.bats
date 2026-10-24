(* npm -- the npm moves of repin (bats-lang/repository-prototype#412).
   Keyword: repin npm.

   Three texts decide what moves; none is a network call, and no YAML is read:

   - the outdated text, `pnpm outdated --format json`: an object with a key for each
     outdated dependency, whose value has the strings `current` (the installed version),
     `wanted` and `latest` (the registry's newest version, of any major);
   - the compatible text, `pnpm outdated --format json --compatible`: the same object, but
     its `latest` is the newest version that the range in package.json allows. pnpm's
     `wanted` is the version of the lockfile, so only this text knows where the range ends.
     A dependency it does not list has no newer version in its range: the ceiling is then
     `wanted`;
   - the times text, one line for each version of each package, three words separated by one
     space: `<name> <version> <published>`, the published time in whole seconds since the
     epoch (1 to 12 digits), as the registry's `time` gives it.

   The candidates of a dependency are the versions in the times text with a plain version tag
   (version.bats: a prerelease is none), of the major of `current`, higher than `current`
   and not higher than the ceiling. The newest candidate that is at least 7 days old at now
   (age.bats) is the target: the dependency is `moved` to it, and `name@version` is a line of
   the update list the job hands to `pnpm update`. When there is no such candidate but there
   are younger ones, the newest of them is `too new`. A `latest` of a higher major than
   `current` is never a target: its own row says `major, not moved`, beside the row of the
   candidates when there is one. A dependency with neither row is `current`. Each row is a
   move record (records.bats) of the kind `npm`; the age is that of the version in the row.
   A version a row names that has no line in the times is an error, and nothing is written. *)

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
   The times text
   ============================================================ *)

fun _word_span {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val byte_value = byte2int0($A.read<byte>(bytes, i))
  in
    if byte_value > 32 && byte_value < 127 then _word_span(bytes, i + 1, j) else false
  end

(* The places of the two spaces of the line bytes[start, stop), each the stop when there is
   no such space *)
fn _spaces {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [first,second:nat | start <= first; first <= second; second <= stop]
    @(int first, int second) = let
  val first = find_byte(bytes, stop, start, 32)
in
  if first >= stop then @(stop, stop)
  else let
    val second = find_byte(bytes, stop, first + 1, 32)
  in @(first, second) end
end

fn _times_line_ok {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (times: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool = let
  val @(first, second) = _spaces(times, start, stop)
in
  if second >= stop then false
  else if first <= start then false
  else if first + 1 >= second then false
  else if ~_word_span(times, start, first) then false
  else if ~_word_span(times, first + 1, second) then false
  else let
    val @(published_ok, _) = parse_seconds(times, second + 1, stop)
  in published_ok end
end

fun _validate_lines {l:agz}{n:pos}{times_len:nat | times_len <= n}{i:nat | i <= times_len}
  .<times_len - i>.
  (times: !$A.borrow(byte, l, n), times_len: int times_len, i: int i, number: int): int =
  if i >= times_len then 0
  else let
    val stop = find_byte(times, times_len, i, 10)
  in
    if ~_times_line_ok(times, i, stop) then number
    else if stop >= times_len then 0
    else _validate_lines(times, times_len, stop + 1, number + 1)
  end

(* The number (from 1) of the first line of times[0, times_len) that is not a times line, else
   0. The last line needs no newline; a blank line is not a times line. *)
#pub fn validate_times {l:agz}{n:pos}{times_len:nat | times_len <= n}
  (times: !$A.borrow(byte, l, n), times_len: int times_len): int

implement validate_times (times, times_len) = _validate_lines(times, times_len, 0, 1)

(* ============================================================
   Choosing a version
   ============================================================ *)

(* Whether the times line times[start, stop) is a candidate of the dependency: its package is
   the name, its version a plain version tag of the major of current, higher than current and
   not higher than the ceiling. In mode 1 the version must also be old enough at now. *)
fn _candidate {times_loc,name_loc,current_loc,ceiling_loc:agz}
  {times_size,name_size,current_size,ceiling_size:pos}
  {stop:nat | stop <= times_size}{start:nat | start <= stop}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  {ceiling_len:nat | ceiling_len <= ceiling_size}
  (times: !$A.borrow(byte, times_loc, times_size), start: int start, stop: int stop,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   ceiling: !$A.borrow(byte, ceiling_loc, ceiling_size), ceiling_len: int ceiling_len,
   mode: int, now: lint): bool = let
  val @(first, second) = _spaces(times, start, stop)
in
  if second >= stop then false
  else if first + 1 >= second then false
  else if ~spans_equal(times, start, first, name, 0, name_len) then false
  else if ~version_ok(times, first + 1, second) then false
  else if version_major(times, first + 1, second) <> version_major(current, 0, current_len)
  then false
  else if version_compare(times, first + 1, second, current, 0, current_len) <= 0 then false
  else if version_compare(times, first + 1, second, ceiling, 0, ceiling_len) > 0 then false
  else if mode = 0 then true
  else let
    val @(_, published) = parse_seconds(times, second + 1, stop)
  in is_candidate(now, published) end
end

(* Whether the version of the line times[start, stop) is higher than the version of the line
   that starts at best. A borrow cannot be passed twice to one call, so the version of the
   best line is copied to compare with. *)
fn _higher {l:agz}{n:pos | n <= 524288}{times_len:nat | times_len <= n}
  {stop:nat | stop <= times_len}{start:nat | start <= stop}{best:nat | best <= times_len}
  (times: !$A.borrow(byte, l, n), times_len: int times_len, start: int start,
   stop: int stop, best: int best): bool = let
  val best_stop = find_byte(times, times_len, best, 10)
  val @(first, second) = _spaces(times, start, stop)
  val @(best_first, best_second) = _spaces(times, best, best_stop)
in
  if first + 1 >= second then false
  else if best_first + 1 >= best_second then true
  else let
    var copy : $B.builder(0) = $B.create()
    val () = put_range(times, best_first + 1, best_second, copy)
    val @(copy_array, copy_len) = $B.to_arr(copy)
    val @(copy_frozen, copy_view) = $A.freeze<byte>(copy_array)
    val higher = version_compare(times, first + 1, second, copy_view, 0, copy_len) > 0
    val () = $A.drop<byte>(copy_frozen, copy_view)
    val () = $A.free<byte>($A.thaw<byte>(copy_frozen))
  in higher end
end

(* The candidate line of the mode with the highest version (the first of equals): whether
   there is one, and where it starts *)
fun _best {times_loc,name_loc,current_loc,ceiling_loc:agz}
  {times_size:pos | times_size <= 524288}{name_size,current_size,ceiling_size:pos}
  {times_len:nat | times_len <= times_size}{i:nat | i <= times_len}
  {best:nat | best <= times_len}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  {ceiling_len:nat | ceiling_len <= ceiling_size} .<times_len - i>.
  (times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len, i: int i,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   ceiling: !$A.borrow(byte, ceiling_loc, ceiling_size), ceiling_len: int ceiling_len,
   mode: int, now: lint, found: bool, best: int best)
  : [chosen:nat | chosen <= times_len] @(bool, int chosen) =
  if i >= times_len then @(found, best)
  else let
    val stop = find_byte(times, times_len, i, 10)
    val matched = _candidate(times, i, stop, name, name_len, current, current_len, ceiling,
      ceiling_len, mode, now)
    val take =
      (if ~matched then false
       else if found then _higher(times, times_len, i, stop, best)
       else true): bool
    val found2 = (if take then true else found): bool
    val best2 = (if take then i else best): [chosen:nat | chosen <= times_len] int chosen
  in
    if stop >= times_len then @(found2, best2)
    else _best(times, times_len, stop + 1, name, name_len, current, current_len, ceiling,
      ceiling_len, mode, now, found2, best2)
  end

(* The published time of the line times[i, stop) when it is the line of the version
   version[version_start, version_stop) of the package name: whether it is, and the time *)
fn _line_published {times_loc,name_loc,version_loc:agz}
  {times_size,name_size,version_size:pos}
  {stop:nat | stop <= times_size}{start:nat | start <= stop}
  {name_len:nat | name_len <= name_size}
  {version_stop:nat | version_stop <= version_size}
  {version_start:nat | version_start <= version_stop}
  (times: !$A.borrow(byte, times_loc, times_size), start: int start, stop: int stop,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   version: !$A.borrow(byte, version_loc, version_size), version_start: int version_start,
   version_stop: int version_stop): @(bool, lint) = let
  val @(first, second) = _spaces(times, start, stop)
in
  if second >= stop then @(false, 0L)
  else if first + 1 >= second then @(false, 0L)
  else if ~spans_equal(times, start, first, name, 0, name_len) then @(false, 0L)
  else if ~spans_equal(times, first + 1, second, version, version_start, version_stop)
  then @(false, 0L)
  else let
    val @(_, published) = parse_seconds(times, second + 1, stop)
  in @(true, published) end
end

(* The published time of the version version[version_start, version_stop) of the package name
   in the times: whether the times have it, and the time *)
fun _published_of {times_loc,name_loc,version_loc:agz}
  {times_size,name_size,version_size:pos}
  {times_len:nat | times_len <= times_size}{i:nat | i <= times_len}
  {name_len:nat | name_len <= name_size}
  {version_stop:nat | version_stop <= version_size}
  {version_start:nat | version_start <= version_stop} .<times_len - i>.
  (times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len, i: int i,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   version: !$A.borrow(byte, version_loc, version_size), version_start: int version_start,
   version_stop: int version_stop): @(bool, lint) =
  if i >= times_len then @(false, 0L)
  else let
    val stop = find_byte(times, times_len, i, 10)
    val @(same, published) =
      _line_published(times, i, stop, name, name_len, version, version_start, version_stop)
  in
    if same then @(true, published)
    else if stop >= times_len then @(false, 0L)
    else _published_of(times, times_len, stop + 1, name, name_len, version, version_start,
      version_stop)
  end

(* ============================================================
   One dependency
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

(* The move record of the dependency name: its current version, the version of the row, the
   age in days and the status *)
fn _put_record {name_loc,current_loc,row_loc:agz}{name_size,current_size,row_size:pos}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  {row_stop:nat | row_stop <= row_size}{row_start:nat | row_start <= row_stop}
  (records: !$B.sized_rope, name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   row: !$A.borrow(byte, row_loc, row_size), row_start: int row_start, row_stop: int row_stop,
   days: int, status: move_status): void = let
  val () = $B.sized_rope_bput(records, "npm\t")
  val () = _copy_span(name, 0, name_len, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = _copy_span(current, 0, current_len, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = _copy_span(row, row_start, row_stop, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_age(records, days)
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_status(records, status)
  val () = $B.sized_rope_bput(records, "\n")
in () end

(* The record of a row whose version is the line of the times that starts at line; the line
   is a candidate line, so it is a times line *)
fn _put_line_record {times_loc,name_loc,current_loc:agz}{times_size,name_size,current_size:pos}
  {times_len:nat | times_len <= times_size}{line:nat | line <= times_len}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  (records: !$B.sized_rope, times: !$A.borrow(byte, times_loc, times_size),
   times_len: int times_len, line: int line,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   now: lint, status: move_status)
  : [version_start,version_stop:nat | version_start <= version_stop; version_stop <= times_size]
    @(int version_start, int version_stop) = let
  val stop = find_byte(times, times_len, line, 10)
  val @(first, second) = _spaces(times, line, stop)
in
  if second >= stop then @(0, 0)
  else if first + 1 >= second then @(0, 0)
  else let
    val @(_, published) = parse_seconds(times, second + 1, stop)
    val () = _put_record(records, name, name_len, current, current_len, times, first + 1,
      second, age_days(now, published), status)
  in @(first + 1, second) end
end

(* The update line `name@version` of the version times[version_start, version_stop) *)
fn _put_update {times_loc,name_loc:agz}{times_size,name_size:pos}
  {name_len:nat | name_len <= name_size}
  {version_stop:nat | version_stop <= times_size}
  {version_start:nat | version_start <= version_stop}
  (updates: !$B.sized_rope, name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   times: !$A.borrow(byte, times_loc, times_size), version_start: int version_start,
   version_stop: int version_stop): void = let
  val () = _copy_span(name, 0, name_len, updates)
  val () = $B.sized_rope_bput(updates, "@")
  val () = _copy_span(times, version_start, version_stop, updates)
  val () = $B.sized_rope_bput(updates, "\n")
in () end

(* The row of a version that is not in the times' lines of the candidates: the version
   row[0, row_len) of the dependency, whose time the times must have. 1 when they have not
   (said on standard error). *)
fn _put_named_record {times_loc,name_loc,current_loc,row_loc:agz}
  {times_size,name_size,current_size,row_size:pos}
  {times_len:nat | times_len <= times_size}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  {row_len:nat | row_len <= row_size}
  (records: !$B.sized_rope, times: !$A.borrow(byte, times_loc, times_size),
   times_len: int times_len, name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   row: !$A.borrow(byte, row_loc, row_size), row_len: int row_len, now: lint,
   status: move_status): int = let
  val @(found, published) = _published_of(times, times_len, 0, name, name_len, row, 0, row_len)
in
  if found then let
    val () = _put_record(records, name, name_len, current, current_len, row, 0, row_len,
      age_days(now, published), status)
  in 0 end
  else let
    val () = prerr! ("repin: the times have no line for ")
    val () = _error_span(name, 0, name_len)
    val () = prerr! (" ")
    val () = _error_span(row, 0, row_len)
    val () = prerrln! ()
  in 1 end
end

(* The rows of the candidates of the dependency name: the target (moved) or the newest
   candidate (too new); whether there is a row, or 1 on an error *)
fn _candidate_rows {times_loc,name_loc,current_loc,ceiling_loc:agz}
  {times_size:pos | times_size <= 524288}{name_size,current_size,ceiling_size:pos}
  {times_len:nat | times_len <= times_size}
  {name_len:nat | name_len <= name_size}{current_len:nat | current_len <= current_size}
  {ceiling_len:nat | ceiling_len <= ceiling_size}
  (times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   ceiling: !$A.borrow(byte, ceiling_loc, ceiling_size), ceiling_len: int ceiling_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): bool = let
  val @(target_found, target) = _best(times, times_len, 0, name, name_len, current,
    current_len, ceiling, ceiling_len, 1, now, false, 0)
in
  if target_found then let
    val @(version_start, version_stop) = _put_line_record(records, times, times_len, target,
      name, name_len, current, current_len, now, Status_moved())
    val () = _put_update(updates, name, name_len, times, version_start, version_stop)
  in true end
  else let
    val @(newest_found, newest) = _best(times, times_len, 0, name, name_len, current,
      current_len, ceiling, ceiling_len, 0, now, false, 0)
  in
    if newest_found then let
      val _ = _put_line_record(records, times, times_len, newest, name, name_len, current,
        current_len, now, Status_too_new())
    in true end
    else false
  end
end

(* What becomes of one dependency at now: its rows appended to records and, for a move, its
   `name@version` line to updates. The facts are its name, its current version, the ceiling of
   its range and its latest version (empty when the registry gave none). 0 when it went well,
   else 1 (said on standard error). *)
#pub fn decide_npm {times_loc,name_loc,current_loc,ceiling_loc,latest_loc:agz}
  {times_size:pos | times_size <= 524288}{name_size,current_size,ceiling_size,latest_size:pos}
  {times_len:nat | times_len <= times_size}
  {name_len:nat | name_len <= name_size}
  {current_len:nat | current_len <= current_size; current_len <= 524288}
  {ceiling_len:nat | ceiling_len <= ceiling_size}{latest_len:nat | latest_len <= latest_size}
  (times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   ceiling: !$A.borrow(byte, ceiling_loc, ceiling_size), ceiling_len: int ceiling_len,
   latest: !$A.borrow(byte, latest_loc, latest_size), latest_len: int latest_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): int

implement decide_npm (times, times_len, name, name_len, current, current_len, ceiling,
  ceiling_len, latest, latest_len, now, records, updates) = let
  val candidates = _candidate_rows(times, times_len, name, name_len, current, current_len,
    ceiling, ceiling_len, now, records, updates)
  val major_row =
    (if latest_len <= 0 then false
     else version_major(latest, 0, latest_len) > version_major(current, 0, current_len)): bool
in
  if major_row then let
    val status = _put_named_record(records, times, times_len, name, name_len, current,
      current_len, latest, latest_len, now, Status_major_not_moved())
  in status end
  else if candidates then 0
  else let
    var row_builder : $B.builder(0) = $B.create()
    val () = put_range(current, 0, current_len, row_builder)
    val @(row_array, row_len) = $B.to_arr(row_builder)
    val @(row_frozen, row_view) = $A.freeze<byte>(row_array)
    val status = _put_named_record(records, times, times_len, name, name_len, current,
      current_len, row_view, row_len, now, Status_current())
    val () = $A.drop<byte>(row_frozen, row_view)
    val () = $A.free<byte>($A.thaw<byte>(row_frozen))
  in status end
end

(* ============================================================
   The JSON texts
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
  {i:nat | i <= dlen}
  .<dlen - i>.
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len, i: int i): bool =
  if i >= dlen then true
  else if byte2int0($A.get<byte>(text, i)) = char2int0(string_get_at(literal, i)) then
    _text_is(text, dlen, literal, i + 1)
  else false

(* Whether the string text[0, dlen) is exactly the literal *)
fn _string_is {l:agz}{cap:pos}{dlen:nat | dlen <= cap}{literal_len:nat}
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len): bool =
  if dlen = g1u2i(string1_length(literal)) then _text_is(text, dlen, literal, 0) else false

fun _strings_equal {first_loc,second_loc:agz}{first_cap,second_cap:pos}
  {first_len:nat | first_len <= first_cap}{second_len:nat | second_len <= second_cap}
  {i:nat | i <= first_len} .<first_len - i>.
  (first: !$A.arr(byte, first_loc, first_cap), first_len: int first_len,
   second: !$A.arr(byte, second_loc, second_cap), second_len: int second_len, i: int i): bool =
  if first_len <> second_len then false
  else if i >= first_len then true
  else if byte2int0($A.get<byte>(first, i)) = byte2int0($A.get<byte>(second, i)) then
    _strings_equal(first, first_len, second, second_len, i + 1)
  else false

(* The string value of the field key of the object fields, copied to the empty builder out:
   whether the object has such a field with a string. The first field of the name counts. *)
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

(* The `latest` string of the field named name[0, name_len) of the object entries, copied to
   the empty builder out: whether that field is an object with such a string *)
fun _find_latest {entries_size:nat}{name_loc:agz}{name_cap:pos}{name_len:nat | name_len <= name_cap} .<entries_size>.
  (entries: !$J.json_entries(entries_size), name: !$A.arr(byte, name_loc, name_cap),
   name_len: int name_len, out: !$B.builder(0) >> $B.builder_v): bool =
  case+ entries of
  | $J.json_entries_nil() => false
  | $J.json_entries_cons(entry_key, entry_key_len, value, rest) =>
    if _strings_equal(entry_key, entry_key_len, name, name_len, 0) then
      (case+ value of
       | $J.json_obj(fields) => _find_field(fields, "latest", out)
       | _ => false)
    else _find_latest(rest, name, name_len, out)

(* The field key of fields as an array and its length, or an empty one when absent *)
fn _field_array {fields_size:nat}{key_len:nat}
  (fields: !$J.json_entries(fields_size), key: string key_len)
  : @([l:agz] $A.arr(byte, l, $B.BUILDER_CAP), [n:nat | n <= $B.BUILDER_CAP] int n) = let
  var text : $B.builder(0) = $B.create()
  val _ = _find_field(fields, key, text)
in $B.to_arr(text) end

(* Whether the span bytes[0, len) is empty or a plain version tag *)
fn _empty_or_version {l:agz}{n:pos}{len:nat | len <= n}
  (bytes: !$A.borrow(byte, l, n), len: int len): bool =
  if len <= 0 then true else version_ok(bytes, 0, len)

(* The ceiling is the range's newest version when pnpm lists the dependency as compatible,
   else the lockfile's, else the current version; a missing time, a current version that is not
   a version tag, or any other fact that is not one is an error said on standard error *)
fn _decide_views {times_loc,name_loc,current_loc,compat_loc,wanted_loc,latest_loc:agz}
  {times_size:pos | times_size <= 524288}
  {name_size,current_size,compat_size,wanted_size,latest_size:pos}
  {times_len:nat | times_len <= times_size}
  {name_len:nat | name_len <= name_size}
  {current_len:nat | current_len <= current_size; current_len <= 524288}
  {compat_len:nat | compat_len <= compat_size}{wanted_len:nat | wanted_len <= wanted_size}
  {latest_len:nat | latest_len <= latest_size}
  (times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len,
   name: !$A.borrow(byte, name_loc, name_size), name_len: int name_len,
   current: !$A.borrow(byte, current_loc, current_size), current_len: int current_len,
   compat: !$A.borrow(byte, compat_loc, compat_size), compat_len: int compat_len,
   wanted: !$A.borrow(byte, wanted_loc, wanted_size), wanted_len: int wanted_len,
   latest: !$A.borrow(byte, latest_loc, latest_size), latest_len: int latest_len,
   now: lint, records: !$B.sized_rope, updates: !$B.sized_rope): int = let
  val shape_ok =
    (if current_len <= 0 then false
     else if ~version_ok(current, 0, current_len) then false
     else if ~_empty_or_version(compat, compat_len) then false
     else if ~_empty_or_version(wanted, wanted_len) then false
     else _empty_or_version(latest, latest_len)): bool
in
  if ~shape_ok then let
    val () = prerr! ("repin: not a version tag in the facts of ")
    val () = _error_span(name, 0, name_len)
    val () = prerrln! ()
  in 1 end
  else if compat_len > 0 then
    decide_npm(times, times_len, name, name_len, current, current_len, compat, compat_len,
      latest, latest_len, now, records, updates)
  else if wanted_len > 0 then
    decide_npm(times, times_len, name, name_len, current, current_len, wanted, wanted_len,
      latest, latest_len, now, records, updates)
  else let
    var ceiling_builder : $B.builder(0) = $B.create()
    val () = put_range(current, 0, current_len, ceiling_builder)
    val @(ceiling_array, ceiling_len) = $B.to_arr(ceiling_builder)
    val @(ceiling_frozen, ceiling_view) = $A.freeze<byte>(ceiling_array)
    val status = decide_npm(times, times_len, name, name_len, current, current_len,
      ceiling_view, ceiling_len, latest, latest_len, now, records, updates)
    val () = $A.drop<byte>(ceiling_frozen, ceiling_view)
    val () = $A.free<byte>($A.thaw<byte>(ceiling_frozen))
  in status end
end

(* The dependency whose key is name[0, name_len) and whose value is value: the facts
   `current`, `wanted` and `latest` of the value and the `latest` of the compatible entries
   decide it *)
fn _entry {value_size,compat_size:nat}{name_loc:agz}{name_cap:pos}{name_len:nat | name_len <= name_cap}
  {times_loc:agz}{times_size:pos | times_size <= 524288}{times_len:nat | times_len <= times_size}
  (name: !$A.arr(byte, name_loc, name_cap), name_len: int name_len,
   value: !$J.json(value_size), compat: !$J.json_entries(compat_size),
   times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len, now: lint,
   records: !$B.sized_rope, updates: !$B.sized_rope): int =
  case+ value of
  | $J.json_obj(fields) => let
      var name_builder : $B.builder(0) = $B.create()
      val _ = _copy_string(name, name_len, name_builder)
      val @(name_array, name_used) = $B.to_arr(name_builder)
      val @(name_frozen, name_view) = $A.freeze<byte>(name_array)
      val @(current_array, current_used) = _field_array(fields, "current")
      val @(current_frozen, current_view) = $A.freeze<byte>(current_array)
      val @(wanted_array, wanted_used) = _field_array(fields, "wanted")
      val @(wanted_frozen, wanted_view) = $A.freeze<byte>(wanted_array)
      val @(latest_array, latest_used) = _field_array(fields, "latest")
      val @(latest_frozen, latest_view) = $A.freeze<byte>(latest_array)
      var compat_builder : $B.builder(0) = $B.create()
      val _ = _find_latest(compat, name, name_len, compat_builder)
      val @(compat_array, compat_used) = $B.to_arr(compat_builder)
      val @(compat_frozen, compat_view) = $A.freeze<byte>(compat_array)
      val status =
        (if name_used <= 0 then let val () = prerrln! ("repin: a dependency with no name") in 1 end
         else _decide_views(times, times_len, name_view, name_used, current_view, current_used,
           compat_view, compat_used, wanted_view, wanted_used, latest_view, latest_used, now,
           records, updates)): int
      val () = $A.drop<byte>(compat_frozen, compat_view)
      val () = $A.free<byte>($A.thaw<byte>(compat_frozen))
      val () = $A.drop<byte>(latest_frozen, latest_view)
      val () = $A.free<byte>($A.thaw<byte>(latest_frozen))
      val () = $A.drop<byte>(wanted_frozen, wanted_view)
      val () = $A.free<byte>($A.thaw<byte>(wanted_frozen))
      val () = $A.drop<byte>(current_frozen, current_view)
      val () = $A.free<byte>($A.thaw<byte>(current_frozen))
      val () = $A.drop<byte>(name_frozen, name_view)
      val () = $A.free<byte>($A.thaw<byte>(name_frozen))
    in status end
  | _ => let val () = prerrln! ("repin: a dependency of the outdated text is not an object") in 1 end

(* Every dependency of the outdated entries, in order; the number of those that did not go well
   (the walk goes on, so each is said) *)
fun _each_entry {entries_size,compat_size:nat}
  {times_loc:agz}{times_size:pos | times_size <= 524288}{times_len:nat | times_len <= times_size}
  .<entries_size>.
  (entries: !$J.json_entries(entries_size), compat: !$J.json_entries(compat_size),
   times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len, now: lint,
   records: !$B.sized_rope, updates: !$B.sized_rope): int =
  case+ entries of
  | $J.json_entries_nil() => 0
  | $J.json_entries_cons(entry_key, entry_key_len, value, rest) => let
      val failed = _entry(entry_key, entry_key_len, value, compat, times, times_len, now,
        records, updates)
      val others = _each_entry(rest, compat, times, times_len, now, records, updates)
    in failed + others end

fn _free_other {size:nat} (root: $J.json(size)): void = $J.json_free(root)

(* The outdated entries in the object outdated_root and the compatible ones in compat_root
   decide the dependencies; the roots are consumed *)
fn _decide_roots {outdated_size,compat_size:nat}
  {times_loc:agz}{times_size:pos | times_size <= 524288}{times_len:nat | times_len <= times_size}
  (outdated_root: $J.json(outdated_size), compat_root: $J.json(compat_size),
   times: !$A.borrow(byte, times_loc, times_size), times_len: int times_len, now: lint,
   records: !$B.sized_rope, updates: !$B.sized_rope): int =
  case+ outdated_root of
  | ~$J.json_obj(entries) =>
    (case+ compat_root of
     | ~$J.json_obj(compat_entries) => let
         val failed = _each_entry(entries, compat_entries, times, times_len, now, records, updates)
         val () = $J.json_entries_free(entries)
         val () = $J.json_entries_free(compat_entries)
       in if failed > 0 then 1 else 0 end
     | other => let
         val () = prerrln! ("repin: the compatible text is not an object")
         val () = $J.json_entries_free(entries)
         val () = _free_other(other)
       in 1 end)
  | other => let
      val () = prerrln! ("repin: the outdated text is not an object")
      val () = _free_other(compat_root)
      val () = _free_other(other)
    in 1 end

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
  (text: !$A.borrow(byte, l, 524288), len: int len, what: string): @(bool, $J.json_v) =
  if len <= 0 then let
    val () = prerrln! ("repin: the ", what, " text is empty")
  in @(false, $J.json_null()) end
  else let
    val exact = $A.alloc<byte>(len)
    val () = _copy_exact(text, len, exact, 0)
    val @(frozen, view) = $A.freeze<byte>(exact)
    val parsed =
      (case+ $J.parse_text(view, len) of
       | ~$R.err(failure) => let
           val position = $J.parse_error_pos(failure)
           val () = prerrln! ("repin: the ", what, " text is not JSON, at byte ", position)
         in @(false, $J.json_null()) end
       | ~$R.ok(root) => @(true, root)): @(bool, $J.json_v)
    val () = $A.drop<byte>(frozen, view)
    val () = $A.free<byte>($A.thaw<byte>(frozen))
  in parsed end

(* What moves, by the outdated text outdated[0, outdated_len), the compatible text and the
   times at now: the rows appended to records and the lines `name@version` of the moves to
   updates. 0 when it went well, else 1 (said on standard error), and then what was appended
   is to be discarded. Each text is in a buffer of 524288 bytes. *)
#pub fn run_npm_texts {outdated_loc,compat_loc,times_loc:agz}
  {outdated_len,compat_len,times_len:nat | outdated_len <= 524288; compat_len <= 524288;
   times_len <= 524288}
  (outdated: !$A.borrow(byte, outdated_loc, 524288), outdated_len: int outdated_len,
   compat: !$A.borrow(byte, compat_loc, 524288), compat_len: int compat_len,
   times: !$A.borrow(byte, times_loc, 524288), times_len: int times_len, now: lint,
   records: !$B.sized_rope, updates: !$B.sized_rope): int

implement run_npm_texts (outdated, outdated_len, compat, compat_len, times, times_len, now,
  records, updates) = let
  val bad_time = validate_times(times, times_len)
in
  if bad_time > 0 then let
    val () = prerrln! ("repin: line ", bad_time, " of the times is not a times line")
  in 1 end
  else let
    val @(outdated_ok, outdated_root) = _parsed(outdated, outdated_len, "outdated")
    val @(compat_ok, compat_root) = _parsed(compat, compat_len, "compatible")
  in
    if ~outdated_ok then let
      val () = _free_other(outdated_root)
      val () = _free_other(compat_root)
    in 1 end
    else if ~compat_ok then let
      val () = _free_other(outdated_root)
      val () = _free_other(compat_root)
    in 1 end
    else _decide_roots(outdated_root, compat_root, times, times_len, now, records, updates)
  end
end
