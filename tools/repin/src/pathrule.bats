(* pathrule -- the repin path rule, written once (bats-lang/repository-prototype#466).
   Keyword: repin path rule.

   The rule (#420): a path is refused when it is empty, starts with `/` or `-`, ends with
   `/`, has an empty, `.` or `..` component, has a character other than letters, digits and
   `._/@+=,-` (a newline included), or has a component that is, in any case, `.git`,
   `.github`, `.gitmodules` or `.gitattributes`, at any depth.

   This module is the pure part: the rule on a span of bytes, and the reading of one line of
   a tar's listing (`tar -tv --numeric-owner --quoting-style=escape`). The streams (the
   paths file and the listing, read a byte at a time, any size) are in pathrule_driver.bats.
   A directory's name has every trailing slash stripped, as tarfile does. A size is any
   number of digits, saturating at 200000000000000000 (20 petabytes of bytes; no file
   system holds a file near it). *)

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

(* Whether the path bytes[start, stop) is refused by the rule (a path that starts or ends with
   `/` has an empty component, which the components refuse) *)
#pub fn path_refused {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): bool

implement path_refused (bytes, start, stop) =
  if stop <= start then true
  else if ~_all_path_chars(bytes, stop, start) then true
  else if _byte(bytes, start) = 45 then true
  else _components_refused(bytes, stop, start, start)

(* Letters of a size: its digits as a number, saturating at 200000000000000000 *)
fun _size_value {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i, value: lint): lint =
  if i >= stop then value
  else if value > 10000000000000000L then 200000000000000000L
  else _size_value(bytes, stop, i + 1, value * 10L + g0int2int_int_lint(_byte(bytes, i) - 48))

fun _all_digits {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i): bool =
  if i >= stop then true
  else if _byte(bytes, i) >= 48 && _byte(bytes, i) <= 57 then _all_digits(bytes, stop, i + 1)
  else false

(* The number written as the digits bytes[start, stop): whether there is at least one digit
   and nothing else, and the value (saturating) *)
#pub fn parse_size {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): @(bool, lint)

implement parse_size (bytes, start, stop) =
  if stop <= start then @(false, 0L)
  else if _all_digits(bytes, stop, start) then @(true, _size_value(bytes, stop, start, 0L))
  else @(false, 0L)

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
   has not that shape; the size is the third word; the name is bytes[name_start,
   name_stop). *)
#pub fn parse_member {l:agz}{n:pos}{stop:nat | stop <= n}{line:nat | line <= stop}
  (bytes: !$A.borrow(byte, l, n), line: int line, stop: int stop)
  : [name_start,name_stop:nat | line <= name_start; name_start <= name_stop; name_stop <= stop]
    @(int, lint, int name_start, int name_stop)

implement parse_member (bytes, line, stop) =
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
        val @(size_ok, size) = parse_size(bytes, size_start, size_stop)
      in
        if size_ok then @(kind, size, time_stop + 1, stop) else @(~1, 0L, line, line)
      end
    end
  end

(* The end of the name of a member: a directory's name loses every trailing slash (as
   tarfile does), a file's is as it is *)
fun _strip_slashes {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop} .<stop - start>.
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [e:nat | start <= e; e <= stop] int e =
  if stop <= start then stop
  else if _byte(bytes, stop - 1) = 47 then _strip_slashes(bytes, start, stop - 1)
  else stop

#pub fn member_end {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), kind: int, start: int start, stop: int stop)
  : [e:nat | start <= e; e <= stop] int e

implement member_end (bytes, kind, start, stop) =
  if kind = 1 then _strip_slashes(bytes, start, stop) else stop

(* Whether the name bytes[name_start, name_stop) is the listed path paths[path_start,
   path_stop) or under it *)
#pub fn name_under_path {name_loc,path_loc:agz}{name_size,path_size:pos}
  {name_stop:nat | name_stop <= name_size}{name_start:nat | name_start <= name_stop}
  {path_stop:nat | path_stop <= path_size}{path_start:nat | path_start <= path_stop}
  (name: !$A.borrow(byte, name_loc, name_size), name_start: int name_start,
   name_stop: int name_stop,
   paths: !$A.borrow(byte, path_loc, path_size), path_start: int path_start,
   path_stop: int path_stop): bool

implement name_under_path (name, name_start, name_stop, paths, path_start, path_stop) =
  if name_stop - name_start = path_stop - path_start then
    spans_equal(name, name_start, name_stop, paths, path_start, path_stop)
  else if name_stop - name_start > path_stop - path_start then
    (if _byte(name, name_start + (path_stop - path_start)) = 47 then
       spans_equal(name, name_start, name_start + (path_stop - path_start),
         paths, path_start, path_stop)
     else false)
  else false
