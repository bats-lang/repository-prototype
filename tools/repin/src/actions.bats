(* actions -- the action pins of repin (bats-lang/repository-prototype#411).
   Keyword: repin actions.

   The releases text is one line per release, four words separated by one space:

     <owner>/<repo> <tag> <commit> <published>

   the commit is 40 lowercase hex digits (the commit the tag points to; for an annotated tag
   the writer of the file has already followed the tag object to its commit) and the
   published time is whole seconds since the epoch (1 to 12 digits). No network is called
   and no YAML is read: a workflow text is read as lines.

   A line holds a pin when it has `<owner>/<repo>[/<path>]@<40 hex>` (a token of
   letters, digits and . _ - /, a '@' and 40 hex digits not followed by a token character).
   A pin of an owner other than bats-lang must be written exactly

     [spaces][- ]uses: <owner>/<repo>[/<path>]@<40 hex> # <version tag>

   the spelling the awk of relock-pins.yml accepts, with the tag of the comment a version
   tag (version.bats); a line that holds a pin in any other spelling is refused, and a text
   with a refused line is not rewritten. The lines between the markers `pin-rewrite begin`
   and `pin-rewrite end` are copied as they are. A pin of bats-lang is left alone (its
   pins move by the workflow pins and the setup action's rule: CLAUDE.md, "CI is pinned").

   What becomes of a pin is decided by the version tags of its repository's releases:
   the target is the highest version of the pin's major version that is a candidate
   (at least 7 days old, age.bats) and higher than the pin's; the pin moves to it and
   the comment becomes its tag. Otherwise a higher major version (any age) is `major, not
   moved`, a higher version of the same major that is younger than 7 days is `too new`,
   and else the pin is `current`. A repository with no release in the text is `current`.
   The pin is never moved to a lower version. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "age.sats"
staload "records.sats"
staload "support.sats"
staload "version.sats"

(* ============================================================
   Characters
   ============================================================ *)

(* A letter, a digit, '.', '_' or '-' *)
fn _name_byte (value: int): bool =
  (value >= 48 && value <= 57) || (value >= 65 && value <= 90) || (value >= 97 && value <= 122)
  || value = 46 || value = 95 || value = 45

fun _name_bytes {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else if _name_byte(byte2int0($A.read<byte>(bytes, i))) then _name_bytes(bytes, i + 1, j)
  else false

fun _hex_bytes {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if (value >= 48 && value <= 57) || (value >= 97 && value <= 102) then
      _hex_bytes(bytes, i + 1, j)
    else false
  end

fun _printable_bytes {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val value = byte2int0($A.read<byte>(bytes, i))
  in
    if value > 32 && value < 127 then _printable_bytes(bytes, i + 1, j) else false
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

(* The first place of bytes[i, limit) that is not a letter, digit, '.', '_' or '-', or limit *)
fun _name_end {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i): [k:nat | i <= k; k <= limit] int k =
  if i >= limit then i
  else if _name_byte(byte2int0($A.read<byte>(bytes, i))) then _name_end(bytes, limit, i + 1)
  else i

(* ============================================================
   The releases text
   ============================================================ *)

(* The places of the three spaces of the line bytes[start, stop), each the stop when there
   is no such space *)
fn _fields {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [first,second,third:nat | start <= first; first <= second; second <= third; third <= stop]
    @(int first, int second, int third) = let
  val first = find_byte(bytes, stop, start, 32)
in
  if first >= stop then @(stop, stop, stop)
  else let
    val second = find_byte(bytes, stop, first + 1, 32)
  in
    if second >= stop then @(first, stop, stop)
    else let
      val third = find_byte(bytes, stop, second + 1, 32)
    in @(first, second, third) end
  end
end

(* Whether bytes[start, stop) is `<owner>/<repo>`: two names and one '/' *)
fn _repo_ok {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool = let
  val slash = find_byte(bytes, stop, start, 47)
in
  if slash <= start then false
  else if slash + 1 >= stop then false
  else if find_byte(bytes, stop, slash + 1, 47) < stop then false
  else _name_bytes(bytes, start, slash) && _name_bytes(bytes, slash + 1, stop)
end

fn _release_line_ok {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (releases: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool = let
  val @(first, second, third) = _fields(releases, start, stop)
in
  if first >= second then false
  else if second >= third then false
  else if third >= stop then false
  else if find_byte(releases, stop, third + 1, 32) < stop then false
  else if third - second <> 41 then false
  else if ~_repo_ok(releases, start, first) then false
  else if ~_printable_bytes(releases, first + 1, second) then false
  else if ~_hex_bytes(releases, second + 1, third) then false
  else let
    val @(published_ok, _) = parse_seconds(releases, third + 1, stop)
  in published_ok end
end

fun _validate_lines {l:agz}{n:pos}{releases_len:nat | releases_len <= n}{i:nat | i <= releases_len}
  .<releases_len - i>.
  (releases: !$A.borrow(byte, l, n), releases_len: int releases_len, i: int i, number: int): int =
  if i >= releases_len then 0
  else let
    val stop = find_byte(releases, releases_len, i, 10)
  in
    if ~_release_line_ok(releases, i, stop) then number
    else if stop >= releases_len then 0
    else _validate_lines(releases, releases_len, stop + 1, number + 1)
  end

(* The number (from 1) of the first line of releases[0, releases_len) that is not a release
   line, else 0. The last line needs no newline; a blank line is not a release line. *)
#pub fn validate_releases {l:agz}{n:pos}{releases_len:nat | releases_len <= n}
  (releases: !$A.borrow(byte, l, n), releases_len: int releases_len): int

implement validate_releases (releases, releases_len) = _validate_lines(releases, releases_len, 0, 1)

(* ============================================================
   Choosing a release
   ============================================================ *)

(* Which release a scan looks for, for a pin of repository R and version V:
   0 the highest version of V's major that is higher than V and a candidate,
   1 the highest version of a major higher than V's,
   2 the highest version of V's major that is higher than V and younger than 7 days,
   3 the release of V's own tag *)
fn _matches {releases_loc,text_loc:agz}{releases_size,text_size:pos}
  {stop:nat | stop <= releases_size}{start:nat | start <= stop}
  {repo_stop:nat | repo_stop <= text_size}{repo_start:nat | repo_start <= repo_stop}
  {tag_stop:nat | tag_stop <= text_size}{tag_start:nat | tag_start <= tag_stop}
  (releases: !$A.borrow(byte, releases_loc, releases_size), start: int start, stop: int stop,
   category: int, text: !$A.borrow(byte, text_loc, text_size), repo_start: int repo_start,
   repo_stop: int repo_stop, tag_start: int tag_start, tag_stop: int tag_stop, now: lint)
  : bool = let
  val @(first, second, third) = _fields(releases, start, stop)
in
  if first >= second then false
  else if third >= stop then false
  else if ~spans_equal(releases, start, first, text, repo_start, repo_stop) then false
  else if category = 3 then spans_equal(releases, first + 1, second, text, tag_start, tag_stop)
  else if ~version_ok(releases, first + 1, second) then false
  else let
    val release_major = version_major(releases, first + 1, second)
    val pin_major = version_major(text, tag_start, tag_stop)
  in
    if category = 1 then release_major > pin_major
    else if release_major <> pin_major then false
    else if version_compare(releases, first + 1, second, text, tag_start, tag_stop) <= 0
    then false
    else let
      val @(_, published) = parse_seconds(releases, third + 1, stop)
    in
      if category = 0 then is_candidate(now, published) else ~is_candidate(now, published)
    end
  end
end

(* Whether the version of the line releases[start, stop) is higher than the version of the
   line that starts at best. A borrow cannot be passed twice to one call, so the tag of the
   best line is copied (at most 524288 bytes, the releases' bound) to compare with. *)
fn _higher {l:agz}{n:pos | n <= 524288}{releases_len:nat | releases_len <= n}
  {stop:nat | stop <= releases_len}{start:nat | start <= stop}{best:nat | best <= releases_len}
  (releases: !$A.borrow(byte, l, n), releases_len: int releases_len, start: int start,
   stop: int stop, best: int best): bool = let
  val best_stop = find_byte(releases, releases_len, best, 10)
  val @(first, second, _) = _fields(releases, start, stop)
  val @(best_first, best_second, _) = _fields(releases, best, best_stop)
in
  if first >= second then false
  else if best_first >= best_second then true
  else let
    var copy : $B.builder(0) = $B.create()
    val () = put_range(releases, best_first + 1, best_second, copy)
    val @(copy_array, copy_len) = $B.to_arr(copy)
    val @(copy_frozen, copy_view) = $A.freeze<byte>(copy_array)
    val higher = version_compare(releases, first + 1, second, copy_view, 0, copy_len) > 0
    val () = $A.drop<byte>(copy_frozen, copy_view)
    val () = $A.free<byte>($A.thaw<byte>(copy_frozen))
  in higher end
end

(* The line of the releases that a scan of the category chooses: whether there is one, and
   where it starts. Among the matching lines the highest version wins, the first of equals. *)
fun _best {releases_loc,text_loc:agz}{releases_size:pos | releases_size <= 524288}
  {text_size:pos}{releases_len:nat | releases_len <= releases_size}
  {i:nat | i <= releases_len}{best:nat | best <= releases_len}
  {repo_stop:nat | repo_stop <= text_size}{repo_start:nat | repo_start <= repo_stop}
  {tag_stop:nat | tag_stop <= text_size}{tag_start:nat | tag_start <= tag_stop}
  .<releases_len - i>.
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   i: int i, category: int, text: !$A.borrow(byte, text_loc, text_size),
   repo_start: int repo_start, repo_stop: int repo_stop, tag_start: int tag_start,
   tag_stop: int tag_stop, now: lint, found: bool, best: int best)
  : [chosen:nat | chosen <= releases_len] @(bool, int chosen) =
  if i >= releases_len then @(found, best)
  else let
    val stop = find_byte(releases, releases_len, i, 10)
    val matched = _matches(releases, i, stop, category, text, repo_start, repo_stop,
      tag_start, tag_stop, now)
    val take =
      (if ~matched then false
       else if found then _higher(releases, releases_len, i, stop, best)
       else true): bool
    val found2 = (if take then true else found): bool
    val best2 = (if take then i else best): [chosen:nat | chosen <= releases_len] int chosen
  in
    if stop >= releases_len then @(found2, best2)
    else _best(releases, releases_len, stop + 1, category, text, repo_start, repo_stop,
      tag_start, tag_stop, now, found2, best2)
  end

(* A scan of the category over all the lines of the releases *)
fn _scan {releases_loc,text_loc:agz}{releases_size:pos | releases_size <= 524288}
  {text_size:pos}{releases_len:nat | releases_len <= releases_size}
  {repo_stop:nat | repo_stop <= text_size}{repo_start:nat | repo_start <= repo_stop}
  {tag_stop:nat | tag_stop <= text_size}{tag_start:nat | tag_start <= tag_stop}
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   text: !$A.borrow(byte, text_loc, text_size), repo_start: int repo_start,
   repo_stop: int repo_stop, tag_start: int tag_start, tag_stop: int tag_stop, now: lint,
   category: int)
  : [chosen:nat | chosen <= releases_len] @(bool, int chosen) =
  _best(releases, releases_len, 0, category, text, repo_start, repo_stop, tag_start, tag_stop,
    now, false, 0)

(* The tag of the line of the releases that starts at start (empty when it has none) *)
fn _release_tag {releases_loc:agz}{releases_size:pos}
  {releases_len:nat | releases_len <= releases_size}{start:nat | start <= releases_len}
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   start: int start)
  : [tag_start,tag_stop:nat | tag_start <= tag_stop; tag_stop <= releases_len]
    @(int tag_start, int tag_stop) = let
  val stop = find_byte(releases, releases_len, start, 10)
  val @(first, second, _) = _fields(releases, start, stop)
in
  if first >= second then @(0, 0) else @(first + 1, second)
end

(* The commit of the line of the releases that starts at start (empty when it has none) *)
fn _release_commit {releases_loc:agz}{releases_size:pos}
  {releases_len:nat | releases_len <= releases_size}{start:nat | start <= releases_len}
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   start: int start)
  : [commit_start,commit_stop:nat | commit_start <= commit_stop; commit_stop <= releases_len]
    @(int commit_start, int commit_stop) = let
  val stop = find_byte(releases, releases_len, start, 10)
  val @(_, second, third) = _fields(releases, start, stop)
in
  if second >= third then @(0, 0) else @(second + 1, third)
end

(* The published time of the line of the releases that starts at start (0 when it has none) *)
fn _release_published {releases_loc:agz}{releases_size:pos}
  {releases_len:nat | releases_len <= releases_size}{start:nat | start <= releases_len}
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   start: int start): lint = let
  val stop = find_byte(releases, releases_len, start, 10)
  val @(_, _, third) = _fields(releases, start, stop)
in
  if third >= stop then 0L
  else let
    val @(_, published) = parse_seconds(releases, third + 1, stop)
  in published end
end

(* What becomes of the pin of the repository text[repo_start, repo_stop) at the version tag
   text[tag_start, tag_stop) at the time now, by the releases: the status; whether a release
   line is what it is about; and where that line starts. For moved, major not moved and too
   new the line is the new version; for current it is the pin's own release, when the
   releases have it. *)
#pub fn pick_release {releases_loc,text_loc:agz}{releases_size:pos | releases_size <= 524288}
  {text_size:pos}{releases_len:nat | releases_len <= releases_size}
  {repo_stop:nat | repo_stop <= text_size}{repo_start:nat | repo_start <= repo_stop}
  {tag_stop:nat | tag_stop <= text_size}{tag_start:nat | tag_start <= tag_stop}
  (releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   text: !$A.borrow(byte, text_loc, text_size), repo_start: int repo_start,
   repo_stop: int repo_stop, tag_start: int tag_start, tag_stop: int tag_stop, now: lint)
  : [line:nat | line <= releases_len] @(move_status, bool, int line)

implement pick_release
  (releases, releases_len, text, repo_start, repo_stop, tag_start, tag_stop, now) = let
  val @(moved, target) = _scan(releases, releases_len, text, repo_start, repo_stop,
    tag_start, tag_stop, now, 0)
in
  if moved then @(Status_moved(), true, target)
  else let
    val @(major_found, major) = _scan(releases, releases_len, text, repo_start, repo_stop,
      tag_start, tag_stop, now, 1)
  in
    if major_found then @(Status_major_not_moved(), true, major)
    else let
      val @(young_found, young) = _scan(releases, releases_len, text, repo_start, repo_stop,
        tag_start, tag_stop, now, 2)
    in
      if young_found then @(Status_too_new(), true, young)
      else let
        val @(own_found, own) = _scan(releases, releases_len, text, repo_start, repo_stop,
          tag_start, tag_stop, now, 3)
      in
        if own_found then @(Status_current(), true, own)
        else @(Status_current(), false, 0)
      end
    end
  end
end

(* ============================================================
   The lines of a workflow text
   ============================================================ *)

(* A character of an `<owner>/<repo>[/<path>]` token: a name byte or '/' *)
fn _token_byte (value: int): bool = _name_byte(value) || value = 47

(* The start of the token that ends at stop, not before start *)
fun _token_start {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  .<stop - start>.
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [k:nat | start <= k; k <= stop] int k =
  if stop <= start then stop
  else if _token_byte(byte2int0($A.read<byte>(bytes, stop - 1))) then
    _token_start(bytes, start, stop - 1)
  else stop

(* Whether the 40 hex digits and the end of the pin start at at + 1 of a '@' at at *)
fn _pin_tail_ok {l:agz}{n:pos}{stop:nat | stop <= n}{at:nat | at < stop}
  (bytes: !$A.borrow(byte, l, n), stop: int stop, at: int at): bool =
  if at + 41 > stop then false
  else if ~_hex_bytes(bytes, at + 1, at + 41) then false
  else if at + 41 = stop then true
  else ~_name_byte(byte2int0($A.read<byte>(bytes, at + 41)))

(* Whether a '@' at at, in the line bytes[start, stop), ends a token holding a '/' and
   starts 40 hex digits: a pin *)
fn _is_pin_at {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  {at:nat | start <= at; at < stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop, at: int at): bool =
  if ~_pin_tail_ok(bytes, stop, at) then false
  else let
    val token = _token_start(bytes, start, at)
  in find_byte(bytes, at, token, 47) < at end

(* The place of the first '@' of a pin in bytes[from, stop), else stop *)
fun _find_pin {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  {from:nat | start <= from; from <= stop} .<stop - from>.
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop, from: int from)
  : [k:nat | from <= k; k <= stop] int k = let
  val at = find_byte(bytes, stop, from, 64)
in
  if at >= stop then stop
  else if _is_pin_at(bytes, start, stop, at) then at
  else _find_pin(bytes, start, stop, at + 1)
end

(* Whether the token bytes[start, stop) has no empty part between its '/' *)
fun _segments_ok {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  {i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop, i: int i): bool =
  if i >= stop then true
  else if byte2int0($A.read<byte>(bytes, i)) <> 47 then _segments_ok(bytes, start, stop, i + 1)
  else if i <= start then false
  else if i + 1 >= stop then false
  else if byte2int0($A.read<byte>(bytes, i + 1)) = 47 then false
  else _segments_ok(bytes, start, stop, i + 1)

(* Whether the ground before a token is `uses:` and blanks, from the place from *)
fn _uses_before {l:agz}{n:pos}{token:nat | token <= n}{from:nat | from <= token}
  (bytes: !$A.borrow(byte, l, n), token: int token, from: int from): bool =
  if from + 5 > token then false
  else if ~span_is(bytes, from, from + 5, "uses:") then false
  else let
    val after = _skip_blank(bytes, token, from + 5)
  in after > from + 5 && after = token end

(* Whether the ground before a token is `[spaces]uses:` and blanks, after an optional `- ` *)
fn _plain_before {l:agz}{n:pos}{token:nat | token <= n}{start:nat | start <= token}
  (bytes: !$A.borrow(byte, l, n), start: int start, token: int token): bool = let
  val first = _skip_blank(bytes, token, start)
in
  if first >= token then false
  else if byte2int0($A.read<byte>(bytes, first)) = 45 then let
    val after = _skip_blank(bytes, token, first + 1)
  in
    if after = first + 1 then false else _uses_before(bytes, token, after)
  end
  else _uses_before(bytes, token, first)
end

(* How a line was dealt with: copied, rewritten, or refused *)
datatype line_end =
  | Line_copied
  | Line_rewritten
  | Line_refused

(* The bytes[start, stop) of a text appended to out as they are *)
fn _copy_span {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (text: !$A.borrow(byte, l, n), start: int start, stop: int stop, out: !$B.sized_rope): void =
  if stop > start then $B.sized_rope_copy(out, text, start, stop) else ()

(* The move record of a pin: kind, name, old and new version, age in days and status.
   The new version is the release's tag, and the pin's own for current. *)
fn _put_record {text_loc,releases_loc:agz}{text_size,releases_size:pos}
  {token:nat | token <= text_size}{at:nat | token <= at; at <= text_size}
  {tag_stop:nat | tag_stop <= text_size}{tag_start:nat | tag_start <= tag_stop}
  {releases_len:nat | releases_len <= releases_size}{line:nat | line <= releases_len}
  (records: !$B.sized_rope, text: !$A.borrow(byte, text_loc, text_size), token: int token,
   at: int at, tag_start: int tag_start, tag_stop: int tag_stop,
   releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   line: int line, status: move_status, has_release: bool, now: lint)
  : void = let
  val @(new_start, new_stop) = _release_tag(releases, releases_len, line)
  val days = (if has_release then age_days(now, _release_published(releases, releases_len, line))
              else 0): int
  val () = $B.sized_rope_bput(records, "action\t")
  val () = _copy_span(text, token, at, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () = _copy_span(text, tag_start, tag_stop, records)
  val () = $B.sized_rope_bput(records, "\t")
  val () =
    (case+ status of
     | Status_current() => _copy_span(text, tag_start, tag_stop, records)
     | _ => _copy_span(releases, new_start, new_stop, records))
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_age(records, days)
  val () = $B.sized_rope_bput(records, "\t")
  val () = put_status(records, status)
  val () = $B.sized_rope_bput(records, "\n")
in () end

(* The line text[start, stop) with its pin at at (the '@'): the record of the pin
   appended to records and the line, rewritten when the pin moves, to out *)
fn _pin_line {text_loc,releases_loc:agz}{text_size:pos}
  {releases_size:pos | releases_size <= 524288}
  {stop:nat | stop <= text_size}{start:nat | start <= stop}{at:nat | start <= at; at < stop}
  {releases_len:nat | releases_len <= releases_size}
  (text: !$A.borrow(byte, text_loc, text_size), start: int start, stop: int stop, at: int at,
   releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   now: lint, out: !$B.sized_rope, records: !$B.sized_rope)
  : line_end = let
  val [token_pos:int] token = _token_start(text, start, at)
in
  if at - token >= 10 && span_is(text, token, token + 10, "bats-lang/") then let
    val () = _copy_span(text, start, stop, out)
  in Line_copied() end
  else if ~_plain_before(text, start, token) then Line_refused()
  else if ~_segments_ok(text, token, at, token) then Line_refused()
  else if at + 41 > stop then Line_refused()
  else let
    val after_pin = at + 41
    val hash = _skip_blank(text, stop, after_pin)
  in
    if hash = after_pin then Line_refused()
    else if hash >= stop then Line_refused()
    else if byte2int0($A.read<byte>(text, hash)) <> 35 then Line_refused()
    else let
      val tag_start = _skip_blank(text, stop, hash + 1)
    in
      if tag_start = hash + 1 then Line_refused()
      else let
        val tag_stop = _name_end(text, stop, tag_start)
      in
        if ~version_ok(text, tag_start, tag_stop) then Line_refused()
        else if _skip_blank(text, stop, tag_stop) < stop then Line_refused()
        else let
          val owner_stop = find_byte(text, at, token, 47)
          val repo_stop =
            (if owner_stop + 1 > at then at
             else find_byte(text, at, owner_stop + 1, 47)): [k:nat | token_pos <= k; k <= at] int k
          val @(status, has_release, line) =
            pick_release(releases, releases_len, text, token, repo_stop, tag_start, tag_stop, now)
          val () = _put_record(records, text, token, at, tag_start, tag_stop, releases,
            releases_len, line, status, has_release, now)
        in
          case+ status of
          | Status_moved() => let
              val @(new_start, new_stop) = _release_tag(releases, releases_len, line)
              val @(commit_start, commit_stop) = _release_commit(releases, releases_len, line)
              val () = _copy_span(text, start, at + 1, out)
              val () = _copy_span(releases, commit_start, commit_stop, out)
              val () = $B.sized_rope_bput(out, " # ")
              val () = _copy_span(releases, new_start, new_stop, out)
            in Line_rewritten() end
          | Status_major_not_moved() =>
              let val () = _copy_span(text, start, stop, out) in Line_copied() end
          | Status_too_new() =>
              let val () = _copy_span(text, start, stop, out) in Line_copied() end
          | Status_current() =>
              let val () = _copy_span(text, start, stop, out) in Line_copied() end
        end
      end
    end
  end
end

(* The line text[start, stop) dealt with; in_region is whether it is between the markers *)
fn _line {text_loc,releases_loc:agz}{text_size:pos}
  {releases_size:pos | releases_size <= 524288}
  {stop:nat | stop <= text_size}{start:nat | start <= stop}
  {releases_len:nat | releases_len <= releases_size}
  (text: !$A.borrow(byte, text_loc, text_size), start: int start, stop: int stop,
   in_region: bool, releases: !$A.borrow(byte, releases_loc, releases_size),
   releases_len: int releases_len, now: lint, out: !$B.sized_rope, records: !$B.sized_rope)
  : line_end =
  if in_region then let val () = _copy_span(text, start, stop, out) in Line_copied() end
  else let
    val at = _find_pin(text, start, stop, start)
  in
    if at >= stop then let val () = _copy_span(text, start, stop, out) in Line_copied() end
    else _pin_line(text, start, stop, at, releases, releases_len, now, out, records)
  end

fun _lines {text_loc,releases_loc:agz}{text_size:pos}
  {releases_size:pos | releases_size <= 524288}{text_len:nat | text_len <= text_size}
  {i:nat | i <= text_len}{releases_len:nat | releases_len <= releases_size}
  .<text_len - i>.
  (text: !$A.borrow(byte, text_loc, text_size), text_len: int text_len, i: int i, number: int,
   in_region: bool, releases: !$A.borrow(byte, releases_loc, releases_size),
   releases_len: int releases_len, now: lint, out: !$B.sized_rope,
   records: !$B.sized_rope, changed: bool)
  : @(int, bool) =
  if i >= text_len then @(0, changed)
  else let
    val stop = find_byte(text, text_len, i, 10)
    val ended = _line(text, i, stop, in_region, releases, releases_len, now, out, records)
  in
    case+ ended of
    | Line_refused() => @(number, changed)
    | _ => let
        val () = if stop < text_len then $B.sized_rope_bput(out, "\n") else ()
        val changed2 = (case+ ended of Line_rewritten() => true | _ => changed): bool
        val region2 =
          (if in_region then ~contains_text(text, stop, i, "pin-rewrite end")
           else contains_text(text, stop, i, "pin-rewrite begin")): bool
      in
        if stop >= text_len then @(0, changed2)
        else _lines(text, text_len, stop + 1, number + 1, region2, releases, releases_len,
          now, out, records, changed2)
      end
  end

(* The workflow text[0, text_len) with each pin moved as the releases say: the number (from
   1) of the first line that holds a pin in a spelling that is not accepted, else 0, and
   whether a line was rewritten. The new text is appended to out and a record for each pin
   examined to records; when a line is refused they hold what came before it and the caller
   discards them. *)
#pub fn rewrite_actions {text_loc,releases_loc:agz}{text_size:pos}
  {releases_size:pos | releases_size <= 524288}{text_len:nat | text_len <= text_size}
  {releases_len:nat | releases_len <= releases_size}
  (text: !$A.borrow(byte, text_loc, text_size), text_len: int text_len,
   releases: !$A.borrow(byte, releases_loc, releases_size), releases_len: int releases_len,
   now: lint, out: !$B.sized_rope, records: !$B.sized_rope)
  : @(int, bool)

implement rewrite_actions (text, text_len, releases, releases_len, now, out, records) =
  _lines(text, text_len, 0, 1, false, releases, releases_len, now, out, records, false)
