(* overlap -- the inputs a pull request removes (bats-lang/repository-prototype#544).
   Keyword: input-overlap. For one changed file: every input of the base text that the head text
   does not declare and the old text (the base one relock cycle earlier) did not mark deprecated
   is an error, printed as a workflow ::error:: command naming the file (the path is
   changes[path_start, path_stop)) and the input. *)

#include "share/atspre_staload.hats"

#use array as A

staload "inputs.sats"
staload "support.sats"

(* The error for one removed input *)
fn _refuse {pl:agz}{pn:pos}{pstop:nat | pstop <= pn}{pstart:nat | pstart <= pstop}
  {tl:agz}{tn:pos}{nstop:nat | nstop <= tn}{nstart:nat | nstart <= nstop}
  (changes: !$A.borrow(byte, pl, pn), path_start: int pstart, path_stop: int pstop,
   base: !$A.borrow(byte, tl, tn), name_start: int nstart, name_stop: int nstop,
   was_deprecated: bool): void = let
  val () = print! ("::error file=")
  val () = print_range(changes, path_start, path_stop)
  val () = print! ("::input ")
  val () = print_range(base, name_start, name_stop)
  val () = print! (" was removed")
in
  if was_deprecated then
    println! (", but the default branch marked it deprecated less than a relock cycle (24 hours) ago: keep it until the mark is a day old (input-overlap)")
  else
    println! (" without being marked deprecated first: keep it working, mark it deprecated (a description that starts with Deprecated, or deprecationMessage) and remove it in a later pull request, a relock cycle after the mark merged (input-overlap)")
end

(* Every input of the base text, from k, that the head text lacks and the old text did not mark
   deprecated: how many *)
fun _removed_from {bl:agz}{bn:pos}{blen:nat | blen <= bn}
  {hl:agz}{hn:pos}{hlen:nat | hlen <= hn}
  {ol:agz}{on:pos}{olen:nat | olen <= on}
  {pl:agz}{pn:pos}{pstop:nat | pstop <= pn}{pstart:nat | pstart <= pstop}{k:nat | k <= blen} .<blen - k>.
  (base: !$A.borrow(byte, bl, bn), base_len: int blen,
   head: !$A.borrow(byte, hl, hn), head_len: int hlen,
   old: !$A.borrow(byte, ol, on), old_len: int olen,
   kind: file_kind, changes: !$A.borrow(byte, pl, pn), path_start: int pstart, path_stop: int pstop,
   k: int k): int =
  if k >= base_len then 0
  else let
    val @(found, name_start, name_stop, base_deprecated) = input_at(base, base_len, kind, k)
  in
    if found then let
      val here =
        (case+ find_input(head, head_len, kind, base, name_start, name_stop) of
         | Input_absent() =>
           (case+ find_input(old, old_len, kind, base, name_start, name_stop) of
            | Input_deprecated() => 0
            | _ => let
                val () = _refuse(changes, path_start, path_stop, base, name_start, name_stop, base_deprecated)
              in 1 end)
         | _ => 0): int
    in here + _removed_from(base, base_len, head, head_len, old, old_len, kind, changes, path_start, path_stop, k + 1) end
    else 0
  end


(* How many inputs of the base text are removed wrongly; each is printed *)
#pub fn removed_inputs {bl:agz}{bn:pos}{blen:nat | blen <= bn}
  {hl:agz}{hn:pos}{hlen:nat | hlen <= hn}
  {ol:agz}{on:pos}{olen:nat | olen <= on}
  {pl:agz}{pn:pos}{pstop:nat | pstop <= pn}{pstart:nat | pstart <= pstop}
  (base: !$A.borrow(byte, bl, bn), base_len: int blen,
   head: !$A.borrow(byte, hl, hn), head_len: int hlen,
   old: !$A.borrow(byte, ol, on), old_len: int olen,
   kind: file_kind, changes: !$A.borrow(byte, pl, pn), path_start: int pstart, path_stop: int pstop): int

implement removed_inputs (base, base_len, head, head_len, old, old_len, kind, changes, path_start, path_stop) =
  _removed_from(base, base_len, head, head_len, old, old_len, kind, changes, path_start, path_stop, 0)
