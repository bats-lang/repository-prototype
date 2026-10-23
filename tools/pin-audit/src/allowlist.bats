(* allowlist -- tools/pin-audit/allowlist.txt, read as bytes
   (bats-lang/repository-prototype#396). Keyword: pin-audit allowlist.

   One entry on each line:

     <repository>/<path> <sha256> [<next sha256>] # <comment>

   The comment is a ticket (<repository>#<number>, then nothing or a space
   and words): every entry names the p2 ticket that says to fix its file. A line that is blank or starts with `#` is
   not an entry. A line that is none of these is a failure of the
   allowlist, named, and never matches a file. Nothing here reads YAML. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

(* What an entry line is: an entry, or why it is not one. Every caller matches
   all six (case+). entry_check gives the first five; Entry_listed_twice is
   what the validation says of a line whose file an earlier line lists. *)
#pub datatype entry_problem =
  | Entry_valid
  | Entry_no_path
  | Entry_no_hash
  | Entry_bad_hashes
  | Entry_no_ticket
  | Entry_listed_twice

(* Which hash of an entry a file has: the current one, the next one, or none
   (no entry lists the file with its hash). Every caller matches all three
   (case+). *)
#pub datatype hash_slot =
  | Hash_current
  | Hash_next
  | Hash_unlisted

(* The comment from space_at (the space after the `#`): a ticket *)
fn _comment_check {l:agz}{entry_end:nat | entry_end <= 524288}{space_at:nat | space_at <= entry_end}
  (text: !$A.borrow(byte, l, 524288), entry_end: int entry_end, space_at: int space_at): entry_problem =
  if space_at + 1 > entry_end then Entry_no_ticket()
  else if byte2int0($A.read<byte>(text, space_at)) != 32 then Entry_no_ticket()
  else if class_end(text, entry_end, space_at, Class_printable()) < entry_end then Entry_no_ticket()
  else let
    val ticket_start = space_at + 1
    val repository_end = class_end(text, entry_end, ticket_start, Class_name())
  in
    if repository_end <= ticket_start then Entry_no_ticket()
    else if repository_end >= entry_end then Entry_no_ticket()
    else if byte2int0($A.read<byte>(text, repository_end)) != 35 then Entry_no_ticket()
    else let
      val digits_end = class_end(text, entry_end, repository_end + 1, Class_digit())
    in
      if digits_end <= repository_end + 1 then Entry_no_ticket()
      else if digits_end >= entry_end then Entry_valid()
      else if byte2int0($A.read<byte>(text, digits_end)) = 32 then Entry_valid()
      else Entry_no_ticket()
    end
  end

(* Whether the line text[entry_start, entry_end) is an entry, and if not why *)
#pub fn entry_check {l:agz}{entry_end:nat | entry_end <= 524288}{entry_start:nat | entry_start <= entry_end}
  (text: !$A.borrow(byte, l, 524288), entry_start: int entry_start, entry_end: int entry_end): entry_problem

implement entry_check (text, entry_start, entry_end) = let
  val repository_end = class_end(text, entry_end, entry_start, Class_name())
in
  if repository_end <= entry_start then Entry_no_path()
  else if repository_end >= entry_end then Entry_no_path()
  else if byte2int0($A.read<byte>(text, repository_end)) != 47 then Entry_no_path()
  else let
    val path_end = class_end(text, entry_end, repository_end + 1, Class_path())
  in
    if path_end <= repository_end + 1 then Entry_no_path()
    else if path_end >= entry_end then Entry_no_hash()
    else if byte2int0($A.read<byte>(text, path_end)) != 32 then Entry_no_path()
    else let
      val first_hash_end = hex_step(text, entry_end, path_end + 1, 64)
    in
      if first_hash_end < 0 then Entry_no_hash()
      else if first_hash_end >= entry_end then Entry_no_ticket()
      else if lit_step(text, entry_end, first_hash_end, " #") >= 0 then _comment_check(text, entry_end, first_hash_end + 2)
      else if byte2int0($A.read<byte>(text, first_hash_end)) != 32 then Entry_bad_hashes()
      else let
        val second_hash_end = hex_step(text, entry_end, first_hash_end + 1, 64)
      in
        if second_hash_end < 0 then Entry_bad_hashes()
        else if second_hash_end >= entry_end then Entry_no_ticket()
        else if lit_step(text, entry_end, second_hash_end, " #") >= 0 then _comment_check(text, entry_end, second_hash_end + 2)
        else Entry_bad_hashes()
      end
    end
  end
end

(* The words for a problem *)
fn _reason (problem: entry_problem): void =
  case+ problem of
  | Entry_valid() => print! ("it is an entry")
  | Entry_no_path() => print! ("it does not start with <repository>/<path> and a space")
  | Entry_no_hash() => print! ("it has no 64-digit lowercase sha256 after its path")
  | Entry_bad_hashes() => print! ("it is not one or two hashes (the current and the next) followed by ` # ` and a comment")
  | Entry_no_ticket() => print! ("it has no ticket comment: `# <repository>#<number>` (the p2 ticket that says to fix the file)")
  | Entry_listed_twice() => print! ("it is listed twice")

(* The end of the key of the entry text[entry_start, entry_end): its first space, or entry_end *)
fn _key_end {l:agz}{entry_end:nat | entry_end <= 524288}{entry_start:nat | entry_start <= entry_end}
  (text: !$A.borrow(byte, l, 524288), entry_start: int entry_start, entry_end: int entry_end): [j:nat | entry_start <= j; j <= entry_end] int j =
  find_byte(text, entry_end, entry_start, 32)

(* Whether the line is an entry *)
fn _is_valid (problem: entry_problem): bool =
  case+ problem of
  | Entry_valid() => true
  | Entry_no_path() => false
  | Entry_no_hash() => false
  | Entry_bad_hashes() => false
  | Entry_no_ticket() => false
  | Entry_listed_twice() => false

(* Whether an entry before entry_start (in text[0, allowlist_len)) has the key
   text[entry_start, key_end). The bound of the comparison is in the types:
   prior_start <= entry_start, so prior_start + (key_end - entry_start) <=
   key_end <= allowlist_len <= 524288. *)
fun _key_before {l:agz}{allowlist_len:nat | allowlist_len <= 524288}{entry_start:nat | entry_start <= allowlist_len}{key_end:nat | entry_start <= key_end; key_end <= allowlist_len}{prior_start:nat | prior_start <= entry_start} .<entry_start - prior_start>.
  (text: !$A.borrow(byte, l, 524288), allowlist_len: int allowlist_len, entry_start: int entry_start, key_end: int key_end, prior_start: int prior_start): bool =
  if prior_start >= entry_start then false
  else let
    val prior_end = line_end(text, allowlist_len, prior_start)
    val prior_key_end = _key_end(text, prior_start, prior_end)
  in
    if prior_end > prior_start && byte2int0($A.read<byte>(text, prior_start)) != 35 && prior_key_end - prior_start = key_end - entry_start
       && range_eq_in(text, entry_start, key_end, prior_start) then true
    else if prior_end >= entry_start then false
    else _key_before(text, allowlist_len, entry_start, key_end, prior_end + 1)
  end

fun _validate {l:agz}{allowlist_len:nat | allowlist_len <= 524288}{i:nat | i <= allowlist_len} .<allowlist_len - i>.
  (text: !$A.borrow(byte, l, 524288), allowlist_len: int allowlist_len, i: int i, line_number: int, entries: int, bad: int): @(int, int) = let
  val j = line_end(text, allowlist_len, i)
  val skip = (j <= i || byte2int0($A.read<byte>(text, i)) = 35): bool
  val problem =
    (if skip then Entry_valid()
     else
       (case+ entry_check(text, i, j) of
        | Entry_valid() =>
            if _key_before(text, allowlist_len, i, _key_end(text, i, j), 0) then Entry_listed_twice() else Entry_valid()
        | other => other)): entry_problem
  val failing = ~_is_valid(problem): bool
  val () =
    if failing then let
      val () = print! ("::error title=pin audit::allowlist.txt line ", line_number, ": ")
      val () = _reason(problem)
    in println! () end
    else ()
  val entries2 = (if skip then entries else entries + 1): int
  val bad2 = (if failing then bad + 1 else bad): int
in
  if j >= allowlist_len then @(entries2, bad2) else _validate(text, allowlist_len, j + 1, line_number + 1, entries2, bad2)
end

(* Checks every entry of the allowlist text[0, allowlist_len): how many entries it has
   and how many of them are failures of the allowlist, each printed with
   its line number and why *)
#pub fn allowlist_validate {l:agz}{allowlist_len:nat | allowlist_len <= 524288}
  (text: !$A.borrow(byte, l, 524288), allowlist_len: int allowlist_len): @(int, int)

implement allowlist_validate (text, allowlist_len) = _validate(text, allowlist_len, 0, 1, 0, 0)

fun _find {allowlist_loc,repository_loc,path_loc,hash_loc:agz}{allowlist_len:nat | allowlist_len <= 524288}{i:nat | i <= allowlist_len}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288}{path_start,path_end:nat | path_start <= path_end; path_end <= 524288} .<allowlist_len - i>.
  (allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, i: int i,
   repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end,
   hash_text: !$A.borrow(byte, hash_loc, 64), line_number: int): @(hash_slot, int) = let
  val j = line_end(allowlist_text, allowlist_len, i)
  val valid =
    (if j > i && byte2int0($A.read<byte>(allowlist_text, i)) != 35 then _is_valid(entry_check(allowlist_text, i, j)) else false): bool
  val key_end = i + (repository_end - repository_start) + 1 + (path_end - path_start)
  val matched =
    (if ~valid then Hash_unlisted()
     else if key_end + 65 > j then Hash_unlisted()
     else if ~range_eq(repository_text, repository_start, repository_end, allowlist_text, i) then Hash_unlisted()
     else if byte2int0($A.read<byte>(allowlist_text, i + (repository_end - repository_start))) != 47 then Hash_unlisted()
     else if ~range_eq(path_text, path_start, path_end, allowlist_text, i + (repository_end - repository_start) + 1) then Hash_unlisted()
     else if byte2int0($A.read<byte>(allowlist_text, key_end)) != 32 then Hash_unlisted()
     else if range_eq(hash_text, 0, 64, allowlist_text, key_end + 1) then Hash_current()
     else if key_end + 130 > j then Hash_unlisted()
     else if byte2int0($A.read<byte>(allowlist_text, key_end + 65)) != 32 then Hash_unlisted()
     else if range_eq(hash_text, 0, 64, allowlist_text, key_end + 66) then Hash_next()
     else Hash_unlisted()): hash_slot
in
  case+ matched of
  | Hash_current() => @(Hash_current(), line_number)
  | Hash_next() => @(Hash_next(), line_number)
  | Hash_unlisted() =>
      if j >= allowlist_len then @(Hash_unlisted(), line_number)
      else _find(allowlist_text, allowlist_len, j + 1, repository_text, repository_start, repository_end, path_text, path_start, path_end, hash_text, line_number + 1)
end

(* The line of the allowlist text[0, allowlist_len) that lists the file
   path_text[path_start, path_end) of the repository
   repository_text[repository_start, repository_end) with the sha256
   hash_text[0, 64) (a valid entry only): which of its two hashes the file
   has (Hash_unlisted when no entry lists it with that hash) and the line
   number of the entry *)
#pub fn allowlist_find {allowlist_loc,repository_loc,path_loc,hash_loc:agz}{allowlist_len:nat | allowlist_len <= 524288}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288}{path_start,path_end:nat | path_start <= path_end; path_end <= 524288}
  (allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len,
   repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end,
   hash_text: !$A.borrow(byte, hash_loc, 64)): @(hash_slot, int)

implement allowlist_find (allowlist_text, allowlist_len, repository_text, repository_start, repository_end, path_text, path_start, path_end, hash_text) =
  _find(allowlist_text, allowlist_len, 0, repository_text, repository_start, repository_end, path_text, path_start, path_end, hash_text, 1)
