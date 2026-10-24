(* skiplist -- tools/pin-audit/skipped.txt, read as bytes
   (bats-lang/repository-prototype#430). Keyword: pin-audit skiplist.

   The repositories the audit does not audit: a test fixture whose workflow
   files and inputs are non-canonical on purpose (relock-scratch exists to test
   the shared relock) can never pass, so the weekly run would be red for a
   reason nobody can fix. One entry on each line:

     <repository> <reason>

   The name is exact (letters, digits, '.', '_' and '-'; no pattern), and the
   reason is words, so no repository is skipped without one. A line that is
   blank or starts with `#` is not an entry. A line that is neither an entry
   nor blank is a failure of the list, named, and skips nothing. Nothing here
   reads YAML. *)

#include "share/atspre_staload.hats"

#use array as A

staload "support.sats"

(* What a line is: an entry, or why it is not one. Every caller matches all
   three (case+). *)
#pub datatype skip_problem =
  | Skip_valid
  | Skip_no_name
  | Skip_no_reason

(* Whether the line text[entry_start, entry_end) is an entry (`<name> <reason>`), and if not why *)
#pub fn skip_check {l:agz}{entry_end:nat | entry_end <= 524288}{entry_start:nat | entry_start <= entry_end}
  (text: !$A.borrow(byte, l, 524288), entry_start: int entry_start, entry_end: int entry_end): skip_problem

implement skip_check (text, entry_start, entry_end) = let
  val name_end = class_end(text, entry_end, entry_start, Class_name())
in
  if name_end <= entry_start then Skip_no_name()
  else if name_end >= entry_end then Skip_no_reason()
  else if byte2int0($A.read<byte>(text, name_end)) != 32 then Skip_no_name()
  else if name_end + 1 >= entry_end then Skip_no_reason()
  else if byte2int0($A.read<byte>(text, name_end + 1)) = 32 then Skip_no_reason()
  else if class_end(text, entry_end, name_end + 1, Class_printable()) < entry_end then Skip_no_reason()
  else Skip_valid()
end

(* The words for a problem *)
fn _reason (problem: skip_problem): void =
  case+ problem of
  | Skip_valid() => print! ("it is an entry")
  | Skip_no_name() => print! ("it does not start with a repository name (letters, digits, '.', '_', '-') and a space")
  | Skip_no_reason() => print! ("it has no reason after the name: `<repository> <words that say why it is skipped>`")

fun _validate {l:agz}{skip_len:nat | skip_len <= 524288}{i:nat | i <= skip_len} .<skip_len - i>.
  (text: !$A.borrow(byte, l, 524288), skip_len: int skip_len, i: int i, line_number: int, entries: int, bad: int): @(int, int) = let
  val j = line_end(text, skip_len, i)
  val not_entry = (j <= i || byte2int0($A.read<byte>(text, i)) = 35): bool
  val problem = (if not_entry then Skip_valid() else skip_check(text, i, j)): skip_problem
  val failing = (case+ problem of | Skip_valid() => false | Skip_no_name() => true | Skip_no_reason() => true): bool
  val () =
    if failing then let
      val () = print! ("::error title=pin audit::skipped.txt line ", line_number, ": ")
      val () = _reason(problem)
    in println! () end
    else ()
  val entries2 = (if not_entry then entries else entries + 1): int
  val bad2 = (if failing then bad + 1 else bad): int
in
  if j >= skip_len then @(entries2, bad2) else _validate(text, skip_len, j + 1, line_number + 1, entries2, bad2)
end

(* Checks every line of the skip list text[0, skip_len): how many entries it has and how many
   of them are failures of the list, each printed with its line number and why *)
#pub fn skiplist_validate {l:agz}{skip_len:nat | skip_len <= 524288}
  (text: !$A.borrow(byte, l, 524288), skip_len: int skip_len): @(int, int)

implement skiplist_validate (text, skip_len) = _validate(text, skip_len, 0, 1, 0, 0)

fun _has {skip_loc,repository_loc:agz}{skip_len:nat | skip_len <= 524288}{i:nat | i <= skip_len}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288} .<skip_len - i>.
  (skip_text: !$A.borrow(byte, skip_loc, 524288), skip_len: int skip_len, i: int i,
   repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): bool = let
  val j = line_end(skip_text, skip_len, i)
  val listed =
    (if j <= i then false
     else if byte2int0($A.read<byte>(skip_text, i)) = 35 then false
     else
       (case+ skip_check(skip_text, i, j) of
        | Skip_valid() => let
            val name_end = class_end(skip_text, j, i, Class_name())
          in
            if name_end - i = repository_end - repository_start then range_eq(repository_text, repository_start, repository_end, skip_text, i)
            else false
          end
        | Skip_no_name() => false
        | Skip_no_reason() => false)): bool
in
  if listed then true
  else if j >= skip_len then false
  else _has(skip_text, skip_len, j + 1, repository_text, repository_start, repository_end)
end

(* Whether the skip list text[0, skip_len) names exactly the repository
   repository_text[repository_start, repository_end) in a valid entry *)
#pub fn skiplist_has {skip_loc,repository_loc:agz}{skip_len:nat | skip_len <= 524288}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288}
  (skip_text: !$A.borrow(byte, skip_loc, 524288), skip_len: int skip_len,
   repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): bool

implement skiplist_has (skip_text, skip_len, repository_text, repository_start, repository_end) =
  _has(skip_text, skip_len, 0, repository_text, repository_start, repository_end)
