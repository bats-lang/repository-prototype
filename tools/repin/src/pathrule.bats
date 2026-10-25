(* pathrule -- the repin path rule, written once (bats-lang/repository-prototype#466).
   Keyword: repin path rule.

   The rule (#420): a path is refused when it is empty, starts with `/` or `-`, ends with
   `/`, has an empty, `.` or `..` component, has a character other than letters, digits and
   `._/@+=,-` (a newline included), or has a component that is, in any case, `.git`,
   `.github`, `.gitmodules` or `.gitattributes`, at any depth.

   Two checks use it, and relock-pins.yml calls them and states no rule of its own:

     check_paths    the lines of repin-paths: at least one path, none refused
     check_members  a tar's listing (`tar -tv --numeric-owner --quoting-style=escape`): every
                    member is a regular file or a directory, its name passes the rule and is a
                    listed path or under one, the sizes add up to at most the cap, and every
                    listed path is a member

   Both append the workflow command `::error::...` to a message when they refuse and return
   1; they return 0 and write nothing when the input is whole. A text is read whole, so the
   listing and the paths are each at most 524288 bytes (a listing is about 60 bytes for each
   member). *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "age.sats"
staload "support.sats"

fn _byte {l:agz}{n:pos}{i:nat | i < n} (bytes: !$A.borrow(byte, l, n), i: int i): int =
  byte2int0($A.read<byte>(bytes, i))

(* Letters, digits and `._/@+=,-` *)
fn _path_char (c: int): bool =
  (c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57)
  || c = 46 || c = 95 || c = 47 || c = 64 || c = 43 || c = 61 || c = 44 || c = 45

fun _all_path_chars {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i): bool =
  if i >= stop then true
  else if _path_char(_byte(bytes, i)) then _all_path_chars(bytes, stop, i + 1)
  else false

fn _lower (c: int): int = if c >= 65 && c <= 90 then c + 32 else c

(* Whether bytes[start, stop) are the lowercase literal, once its letters are lowercased *)
fun _lower_from {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop}{literal_len:nat}
  {at:nat | at <= literal_len} .<literal_len - at>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i, literal: string literal_len,
   literal_len: int literal_len, at: int at): bool =
  if at >= literal_len then i = stop
  else if i >= stop then false
  else if _lower(_byte(bytes, i)) = char2int0(string_get_at(literal, at)) then
    _lower_from(bytes, stop, i + 1, literal, literal_len, at + 1)
  else false

fn _lower_is {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}{literal_len:nat}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop,
   literal: string literal_len): bool =
  _lower_from(bytes, stop, start, literal, g1u2i(string1_length(literal)), 0)

(* The component bytes[start, stop): empty, `.`, `..` or a name git reads *)
fn _component_refused {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool =
  if stop = start then true
  else if _lower_is(bytes, start, stop, ".") then true
  else if _lower_is(bytes, start, stop, "..") then true
  else if _lower_is(bytes, start, stop, ".git") then true
  else if _lower_is(bytes, start, stop, ".github") then true
  else if _lower_is(bytes, start, stop, ".gitmodules") then true
  else _lower_is(bytes, start, stop, ".gitattributes")

(* Whether a component of bytes[component, stop), searching from i, is refused *)
fun _components_refused {l:agz}{n:pos}{stop:nat | stop <= n}{component:nat | component <= stop}
  {i:nat | component <= i; i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, component: int component, i: int i): bool =
  if i >= stop then _component_refused(bytes, component, stop)
  else if _byte(bytes, i) = 47 then
    (if _component_refused(bytes, component, i) then true
     else _components_refused(bytes, stop, i + 1, i + 1))
  else _components_refused(bytes, stop, component, i + 1)

(* Whether the path bytes[start, stop) is refused by the rule *)
#pub fn path_refused {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool

implement path_refused (bytes, start, stop) =
  if stop <= start then true
  else if ~_all_path_chars(bytes, stop, start) then true
  else if _byte(bytes, start) = 47 || _byte(bytes, start) = 45 then true
  else if _byte(bytes, stop - 1) = 47 then true
  else _components_refused(bytes, stop, start, start)

(* The paths text bytes[0, len), a path on each line (an empty line is none), scanned from
   i: 0 when there is a path and none is refused, 1 when there is no path, 2 with the span
   of the first refused path *)
fun _paths_scan {l:agz}{n:pos}{len:nat | len <= n}{i:nat | i <= len} .<len - i>.
  (bytes: !$A.borrow(byte, l, n), len: int len, i: int i, seen: int)
  : [s,e:nat | s <= e; e <= len] @(int, int s, int e) =
  if i >= len then (if seen > 0 then @(0, 0, 0) else @(1, 0, 0))
  else let
    val stop = find_byte(bytes, len, i, 10)
    val next = (if stop >= len then len else stop + 1): [k:nat | i < k; k <= len] int k
  in
    if stop = i then _paths_scan(bytes, len, next, seen)
    else if path_refused(bytes, i, stop) then @(2, i, stop)
    else _paths_scan(bytes, len, next, seen + 1)
  end

fn _put_span {l:agz}{n:pos}{start,stop:nat | start <= stop; stop <= n}
  (message: !$B.sized_rope, bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): void =
  $B.sized_rope_copy(message, bytes, start, stop)

(* The paths text bytes[0, len) checked: 0 when there is a path and none is refused, else 1
   with the command `::error::` and its words appended to message *)
#pub fn check_paths {l:agz}{n:pos}{len:nat | len <= n}
  (bytes: !$A.borrow(byte, l, n), len: int len, message: !$B.sized_rope): int

implement check_paths (bytes, len, message) = let
  val @(code, start, stop) = _paths_scan(bytes, len, 0, 0)
in
  if code = 0 then 0
  else if code = 1 then let
    val () = $B.sized_rope_bput(message, "::error::repin-paths is empty: nothing would be committed\n")
  in 1 end
  else let
    val () = $B.sized_rope_bput(message, "::error::repin-paths names a path that is refused: ")
    val () = _put_span(message, bytes, start, stop)
    val () = $B.sized_rope_bput(message, "\n")
  in 1 end
end

(* ============================================================
   A tar's listing
   ============================================================ *)

fun _skip_spaces {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i)
  : [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if _byte(bytes, i) = 32 then _skip_spaces(bytes, limit, i + 1)
  else i

fun _skip_token {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i)
  : [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if _byte(bytes, i) = 32 then i
  else _skip_token(bytes, limit, i + 1)

(* One line of `tar -tv --numeric-owner` as bytes[line, stop): the mode (whose first letter
   is the type), owner/group, size, date, time and the name, separated by spaces. The kind
   is 0 for a regular file, 1 for a directory, 2 for any other type, and -1 when the line
   has not that shape; the size is the third word (at most 12 digits); the name is
   bytes[name_start, name_stop). *)
fn _parse_line {l:agz}{n:pos}{stop:nat | stop <= n}{line:nat | line <= stop}
  (bytes: !$A.borrow(byte, l, n), line: int line, stop: int stop)
  : [name_start,name_stop:nat | line <= name_start; name_start <= name_stop; name_stop <= stop]
    @(int, lint, int name_start, int name_stop) =
  if line >= stop then @(~1, 0L, line, line)
  else let
    val first = _byte(bytes, line)
  in
    if first != 45 && first != 100 then @(2, 0L, line, line)
    else let
      val mode_stop = _skip_token(bytes, stop, line)
      val owner_start = _skip_spaces(bytes, stop, mode_stop)
      val owner_stop = _skip_token(bytes, stop, owner_start)
      val size_start = _skip_spaces(bytes, stop, owner_stop)
      val size_stop = _skip_token(bytes, stop, size_start)
      val date_start = _skip_spaces(bytes, stop, size_stop)
      val date_stop = _skip_token(bytes, stop, date_start)
      val time_start = _skip_spaces(bytes, stop, date_stop)
      val time_stop = _skip_token(bytes, stop, time_start)
      val kind = (if first = 100 then 1 else 0): int
    in
      if time_stop >= stop then @(~1, 0L, line, line)
      else if mode_stop = line || owner_stop = owner_start || size_stop = size_start
              || date_stop = date_start || time_stop = time_start then
        @(~1, 0L, line, line)
      else let
        val @(size_ok, size) = parse_seconds(bytes, size_start, size_stop)
      in
        if size_ok then @(kind, size, time_stop + 1, stop) else @(~1, 0L, line, line)
      end
    end
  end

(* The name of a member without the slash that ends a directory's *)
fn _member_end {l:agz}{n:pos}{stop:nat | stop <= n}{name_start:nat | name_start <= stop}
  (bytes: !$A.borrow(byte, l, n), kind: int, name_start: int name_start, name_stop: int stop)
  : [e:nat | name_start <= e; e <= stop] int e =
  if kind != 1 then name_stop
  else if name_stop <= name_start then name_stop
  else if _byte(bytes, name_stop - 1) = 47 then name_stop - 1
  else name_stop

(* Whether the name bytes[name_start, name_stop) is the listed path paths[path_start, path_stop)
   or under it *)
fn _under {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {name_stop:nat | name_stop <= listing_size}{name_start:nat | name_start <= name_stop}
  {path_stop:nat | path_stop <= paths_size}{path_start:nat | path_start <= path_stop}
  (listing: !$A.borrow(byte, listing_loc, listing_size), name_start: int name_start,
   name_stop: int name_stop,
   paths: !$A.borrow(byte, paths_loc, paths_size), path_start: int path_start,
   path_stop: int path_stop): bool =
  if name_stop - name_start = path_stop - path_start then
    spans_equal(listing, name_start, name_stop, paths, path_start, path_stop)
  else if name_stop - name_start > path_stop - path_start then
    (if _byte(listing, name_start + (path_stop - path_start)) = 47 then
       spans_equal(listing, name_start, name_start + (path_stop - path_start),
         paths, path_start, path_stop)
     else false)
  else false

(* Whether the name is a listed path or under one: the paths text paths[0, paths_len)
   searched from i *)
fun _under_any {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {name_stop:nat | name_stop <= listing_size}{name_start:nat | name_start <= name_stop}
  {paths_len:nat | paths_len <= paths_size}{i:nat | i <= paths_len} .<paths_len - i>.
  (listing: !$A.borrow(byte, listing_loc, listing_size), name_start: int name_start,
   name_stop: int name_stop,
   paths: !$A.borrow(byte, paths_loc, paths_size), paths_len: int paths_len, i: int i): bool =
  if i >= paths_len then false
  else let
    val stop = find_byte(paths, paths_len, i, 10)
    val next = (if stop >= paths_len then paths_len else stop + 1)
      : [k:nat | i < k; k <= paths_len] int k
  in
    if stop > i && _under(listing, name_start, name_stop, paths, i, stop) then true
    else _under_any(listing, name_start, name_stop, paths, paths_len, next)
  end

(* The members of listing[0, listing_len) from i: 0 when each is a regular file or a
   directory whose name passes the rule and is a listed path or under one, and the sizes
   add up to at most the cap; else the code and the span of the finding: 1 a name (the
   name), 2 a type (the line), 3 the cap (empty), 4 a line of another shape (the line) *)
fun _members_scan {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {listing_len:nat | listing_len <= listing_size}{paths_len:nat | paths_len <= paths_size}
  {i:nat | i <= listing_len} .<listing_len - i>.
  (listing: !$A.borrow(byte, listing_loc, listing_size), listing_len: int listing_len,
   paths: !$A.borrow(byte, paths_loc, paths_size), paths_len: int paths_len,
   cap: lint, i: int i, total: lint)
  : [s,e:nat | s <= e; e <= listing_len] @(int, int s, int e) =
  if i >= listing_len then @(0, 0, 0)
  else let
    val stop = find_byte(listing, listing_len, i, 10)
    val next = (if stop >= listing_len then listing_len else stop + 1)
      : [k:nat | i < k; k <= listing_len] int k
    val @(kind, size, name_start, name_stop) = _parse_line(listing, i, stop)
  in
    if kind < 0 then @(4, i, stop)
    else if kind = 2 then @(2, i, stop)
    else let
      val name_end = _member_end(listing, kind, name_start, name_stop)
    in
      if path_refused(listing, name_start, name_end) then @(1, name_start, name_end)
      else if ~_under_any(listing, name_start, name_end, paths, paths_len, 0) then
        @(1, name_start, name_end)
      else if total + size > cap then @(3, 0, 0)
      else _members_scan(listing, listing_len, paths, paths_len, cap, next, total + size)
    end
  end

(* Whether a member of listing[0, listing_len), from i, is exactly the path
   paths[path_start, path_stop) *)
fun _holds {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {listing_len:nat | listing_len <= listing_size}
  {path_stop:nat | path_stop <= paths_size}{path_start:nat | path_start <= path_stop}
  {i:nat | i <= listing_len} .<listing_len - i>.
  (listing: !$A.borrow(byte, listing_loc, listing_size), listing_len: int listing_len,
   paths: !$A.borrow(byte, paths_loc, paths_size), path_start: int path_start,
   path_stop: int path_stop, i: int i): bool =
  if i >= listing_len then false
  else let
    val stop = find_byte(listing, listing_len, i, 10)
    val next = (if stop >= listing_len then listing_len else stop + 1)
      : [k:nat | i < k; k <= listing_len] int k
    val @(kind, _, name_start, name_stop) = _parse_line(listing, i, stop)
  in
    if kind < 0 || kind = 2 then _holds(listing, listing_len, paths, path_start, path_stop, next)
    else let
      val name_end = _member_end(listing, kind, name_start, name_stop)
    in
      if spans_equal(listing, name_start, name_end, paths, path_start, path_stop) then true
      else _holds(listing, listing_len, paths, path_start, path_stop, next)
    end
  end

(* The first listed path of paths[0, paths_len), from i, that is no member of the listing:
   its span, empty when every one is a member *)
fun _first_missing {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {listing_len:nat | listing_len <= listing_size}{paths_len:nat | paths_len <= paths_size}
  {i:nat | i <= paths_len} .<paths_len - i>.
  (listing: !$A.borrow(byte, listing_loc, listing_size), listing_len: int listing_len,
   paths: !$A.borrow(byte, paths_loc, paths_size), paths_len: int paths_len, i: int i)
  : [s,e:nat | s <= e; e <= paths_len] @(int s, int e) =
  if i >= paths_len then @(0, 0)
  else let
    val stop = find_byte(paths, paths_len, i, 10)
    val next = (if stop >= paths_len then paths_len else stop + 1)
      : [k:nat | i < k; k <= paths_len] int k
  in
    if stop = i then _first_missing(listing, listing_len, paths, paths_len, next)
    else if _holds(listing, listing_len, paths, i, stop, 0) then
      _first_missing(listing, listing_len, paths, paths_len, next)
    else @(i, stop)
  end

(* The listing listing[0, listing_len) of a tar checked against the listed paths
   paths[0, paths_len) and the cap on the sizes of its files: 0 when the paths pass the
   rule and every member is a regular file or a directory that passes it, is a listed path
   or under one, within the cap, and every listed path is a member; else 1 with the command
   `::error::` and its words appended to message *)
#pub fn check_members {listing_loc,paths_loc:agz}{listing_size,paths_size:pos}
  {listing_len:nat | listing_len <= listing_size}{paths_len:nat | paths_len <= paths_size}
  (listing: !$A.borrow(byte, listing_loc, listing_size), listing_len: int listing_len,
   paths: !$A.borrow(byte, paths_loc, paths_size), paths_len: int paths_len,
   cap: lint, message: !$B.sized_rope): int

implement check_members (listing, listing_len, paths, paths_len, cap, message) =
  if check_paths(paths, paths_len, message) != 0 then 1
  else let
    val @(code, start, stop) = _members_scan(listing, listing_len, paths, paths_len, cap, 0, 0L)
  in
    if code = 1 then let
      val () = $B.sized_rope_bput(message,
        "::error::a member outside the listed paths or with a refused name: ")
      val () = _put_span(message, listing, start, stop)
      val () = $B.sized_rope_bput(message, "\n")
    in 1 end
    else if code = 2 then let
      val () = $B.sized_rope_bput(message,
        "::error::a member that is not a regular file or a directory: ")
      val () = _put_span(message, listing, start, stop)
      val () = $B.sized_rope_bput(message, "\n")
    in 1 end
    else if code = 3 then let
      val () = $B.sized_rope_bput(message,
        "::error::the repinned files are over repin-max-bytes\n")
    in 1 end
    else if code = 4 then let
      val () = $B.sized_rope_bput(message, "::error::a line of the tar listing that is no member: ")
      val () = _put_span(message, listing, start, stop)
      val () = $B.sized_rope_bput(message, "\n")
    in 1 end
    else let
      val @(missing_start, missing_stop) = _first_missing(listing, listing_len, paths, paths_len, 0)
    in
      if missing_stop > missing_start then let
        val () = $B.sized_rope_bput(message, "::error::the repinned files do not hold ")
        val () = _put_span(message, paths, missing_start, missing_stop)
        val () = $B.sized_rope_bput(message, "\n")
      in 1 end
      else 0
    end
  end
