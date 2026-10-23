(* allowlist -- tools/pin-audit/allowlist.txt, read as bytes
   (bats-lang/repository-prototype#396). Keyword: pin-audit allowlist.

   One entry on each line:

     <repository>/<path> <sha256> [<next sha256>] # <comment>

   The comment is a ticket (<repository>#<number>, then nothing or a space
   and words) or `canonical`. A line that is blank or starts with `#` is
   not an entry. A line that is none of these is a failure of the
   allowlist, named, and never matches a file. Nothing here reads YAML. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

(* Why an entry line is not an entry: 0 it is one, 1 it does not start with
   <repository>/<path>, 2 it has no 64-digit lowercase sha256 after its
   path, 3 it has something other than one or two hashes and a comment, 4
   its comment names no ticket *)

(* The comment from c (the space after the `#`): `canonical`, or a ticket *)
fn _comment_check {l:agz}{le:nat | le <= 524288}{c:nat | c <= le}
  (b: !$A.borrow(byte, l, 524288), le: int le, c: int c): int =
  if c + 1 > le then 4
  else if byte2int0($A.read<byte>(b, c)) != 32 then 4
  else if class_end(b, le, c, 3) < le then 4
  else let
    val q = c + 1
    val canon = lit_step(b, le, q, "canonical")
  in
    if canon >= le then 0
    else if canon >= 0 && byte2int0($A.read<byte>(b, canon)) = 32 then 0
    else let
      val re = class_end(b, le, q, 1)
    in
      if re <= q then 4
      else if re >= le then 4
      else if byte2int0($A.read<byte>(b, re)) != 35 then 4
      else let
        val de = class_end(b, le, re + 1, 0)
      in
        if de <= re + 1 then 4
        else if de >= le then 0
        else if byte2int0($A.read<byte>(b, de)) = 32 then 0
        else 4
      end
    end
  end

(* The reason code of the line b[ls, le) *)
#pub fn entry_check {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (b: !$A.borrow(byte, l, 524288), ls: int ls, le: int le): int

implement entry_check (b, ls, le) = let
  val rs = class_end(b, le, ls, 1)
in
  if rs <= ls then 1
  else if rs >= le then 1
  else if byte2int0($A.read<byte>(b, rs)) != 47 then 1
  else let
    val pe = class_end(b, le, rs + 1, 2)
  in
    if pe <= rs + 1 then 1
    else if pe >= le then 2
    else if byte2int0($A.read<byte>(b, pe)) != 32 then 1
    else let
      val e1 = hex_step(b, le, pe + 1, 64)
    in
      if e1 < 0 then 2
      else if e1 >= le then 4
      else if lit_step(b, le, e1, " #") >= 0 then _comment_check(b, le, e1 + 2)
      else if byte2int0($A.read<byte>(b, e1)) != 32 then 3
      else let
        val e2 = hex_step(b, le, e1 + 1, 64)
      in
        if e2 < 0 then 3
        else if e2 >= le then 4
        else if lit_step(b, le, e2, " #") >= 0 then _comment_check(b, le, e2 + 2)
        else 3
      end
    end
  end
end

(* The words for a reason code *)
fn _reason (code: int): void =
  if code = 1 then print! ("it does not start with <repository>/<path> and a space")
  else if code = 2 then print! ("it has no 64-digit lowercase sha256 after its path")
  else if code = 3 then print! ("it is not one or two hashes (the current and the next) followed by ` # ` and a comment")
  else if code = 4 then print! ("it has no ticket comment: `# <repository>#<number>` (the p2 ticket that says to fix the file), or `# canonical`")
  else print! ("it is listed twice")

(* The end of the key of the entry b[ls, le): its first space, or le *)
fn _key_end {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (b: !$A.borrow(byte, l, 524288), ls: int ls, le: int le): [j:nat | ls <= j; j <= le] int j =
  find_byte(b, le, ls, 32)

(* Whether an entry before ls (in b[0, ak)) has the key b[ls, ke) *)
fun _key_before {l:agz}{ak:nat | ak <= 524288}{ls:nat | ls <= ak}{ke:nat | ls <= ke; ke <= ak}{p:nat | p <= ls} .<ls - p>.
  (b: !$A.borrow(byte, l, 524288), ak: int ak, ls: int ls, ke: int ke, p: int p): bool =
  if p >= ls then false
  else let
    val pe = line_end(b, ak, p)
    val pk = _key_end(b, p, pe)
  in
    if pe > p && byte2int0($A.read<byte>(b, p)) != 35 && pk - p = ke - ls
       && p + (ke - ls) <= 524288 && range_eq_in(b, ls, ke, p) then true
    else if pe >= ls then false
    else _key_before(b, ak, ls, ke, pe + 1)
  end

fun _validate {l:agz}{ak:nat | ak <= 524288}{i:nat | i <= ak} .<ak - i>.
  (b: !$A.borrow(byte, l, 524288), ak: int ak, i: int i, no: int, entries: int, bad: int): @(int, int) = let
  val j = line_end(b, ak, i)
  val skip = (j <= i || byte2int0($A.read<byte>(b, i)) = 35): bool
  val code = (if skip then 0 else entry_check(b, i, j)): int
  val dup = (if skip || code != 0 then false else _key_before(b, ak, i, _key_end(b, i, j), 0)): bool
  val () =
    if code != 0 || dup then let
      val () = print! ("::error title=pin audit::allowlist.txt line ", no, ": ")
      val () = _reason(if dup then 5 else code)
    in println! () end
    else ()
  val entries2 = (if skip then entries else entries + 1): int
  val bad2 = (if code != 0 || dup then bad + 1 else bad): int
in
  if j >= ak then @(entries2, bad2) else _validate(b, ak, j + 1, no + 1, entries2, bad2)
end

(* Checks every entry of the allowlist b[0, ak): how many entries it has
   and how many of them are failures of the allowlist, each printed with
   its line number and why *)
#pub fn allowlist_validate {l:agz}{ak:nat | ak <= 524288}
  (b: !$A.borrow(byte, l, 524288), ak: int ak): @(int, int)

implement allowlist_validate (b, ak) = _validate(b, ak, 0, 1, 0, 0)

fun _find {l,lr,lp,lh:agz}{ak:nat | ak <= 524288}{i:nat | i <= ak}{s,e:nat | s <= e; e <= 524288}{fs,fe:nat | fs <= fe; fe <= 524288} .<ak - i>.
  (ab: !$A.borrow(byte, l, 524288), ak: int ak, i: int i,
   nb: !$A.borrow(byte, lr, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe,
   hb: !$A.borrow(byte, lh, 64), no: int): @(int, int, int) = let
  val j = line_end(ab, ak, i)
  val here = (if j > i && byte2int0($A.read<byte>(ab, i)) != 35 then entry_check(ab, i, j) else 1): int
  val key_end = i + (e - s) + 1 + (fe - fs)
  val matched =
    (if here != 0 then 0
     else if key_end + 65 > j then 0
     else if ~range_eq(nb, s, e, ab, i) then 0
     else if byte2int0($A.read<byte>(ab, i + (e - s))) != 47 then 0
     else if ~range_eq(pb, fs, fe, ab, i + (e - s) + 1) then 0
     else if byte2int0($A.read<byte>(ab, key_end)) != 32 then 0
     else if range_eq(hb, 0, 64, ab, key_end + 1) then 1
     else if key_end + 130 > j then 0
     else if byte2int0($A.read<byte>(ab, key_end + 65)) != 32 then 0
     else if range_eq(hb, 0, 64, ab, key_end + 66) then 2
     else 0): int
in
  if matched > 0 then @(i, matched, no)
  else if j >= ak then @(~1, 0, no)
  else _find(ab, ak, j + 1, nb, s, e, pb, fs, fe, hb, no + 1)
end

(* The line of the allowlist b[0, ak) that lists the file pb[fs, fe) of the
   repository nb[s, e) with the sha256 hb[0, 64) (a valid entry only), as
   its start, which of its two hashes (1 current, 2 next) and its line
   number; the start is ~1 when no entry lists it with that hash *)
#pub fn allowlist_find {l,lr,lp,lh:agz}{ak:nat | ak <= 524288}{s,e:nat | s <= e; e <= 524288}{fs,fe:nat | fs <= fe; fe <= 524288}
  (ab: !$A.borrow(byte, l, 524288), ak: int ak,
   nb: !$A.borrow(byte, lr, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe,
   hb: !$A.borrow(byte, lh, 64)): @(int, int, int)

implement allowlist_find (ab, ak, nb, s, e, pb, fs, fe, hb) = _find(ab, ak, 0, nb, s, e, pb, fs, fe, hb, 1)
