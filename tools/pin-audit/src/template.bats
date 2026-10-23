(* template -- a file equal to a template with its holes filled
   (bats-lang/repository-prototype#396). Keyword: pin-audit template.

   The template is split at its markers and each segment is compared with
   the file byte for byte; a hole's value is checked against its class:
   @@COMMIT@@ is exactly 40 lowercase hexadecimal digits, @@COMMENT@@ is a
   run of one or more printable ASCII characters (space to `~`, so it ends
   at the end of the line), @@MINUTE@@ is one or two decimal digits. Any
   other text is a segment. The file must end where the template ends.
   Nothing here reads YAML. *)

#include "share/atspre_staload.hats"

#use array as A

staload "support.sats"

fun _walk {l,lf:agz}{tk,fk:nat | tk <= 524288; fk <= 524288}{t:nat | t <= tk}{f:nat | f <= fk} .<tk - t>.
  (tb: !$A.borrow(byte, l, 524288), tk: int tk, t: int t,
   fb: !$A.borrow(byte, lf, 524288), fk: int fk, f: int f): bool =
  if t >= tk then f >= fk
  else let
    val commit = lit_step(tb, tk, t, "@@COMMIT@@")
  in
    if commit >= 0 then let
      val h = hex_step(fb, fk, f, 40)
    in if h >= 0 then _walk(tb, tk, commit, fb, fk, h) else false end
    else let
      val comment = lit_step(tb, tk, t, "@@COMMENT@@")
    in
      if comment >= 0 then let
        val e = class_end(fb, fk, f, 3)
      in if e > f then _walk(tb, tk, comment, fb, fk, e) else false end
      else let
        val minute = lit_step(tb, tk, t, "@@MINUTE@@")
      in
        if minute >= 0 then let
          val d = digits_upto_two(fb, fk, f)
        in if d >= 1 then _walk(tb, tk, minute, fb, fk, f + d) else false end
        else if f >= fk then false
        else if byte2int0($A.read<byte>(tb, t)) = byte2int0($A.read<byte>(fb, f)) then _walk(tb, tk, t + 1, fb, fk, f + 1)
        else false
      end
    end
  end

(* Whether the file fb[0, fk) is the template tb[0, tk) with its holes filled *)
#pub fn template_matches {l,lf:agz}{tk,fk:nat | tk <= 524288; fk <= 524288}
  (tb: !$A.borrow(byte, l, 524288), tk: int tk,
   fb: !$A.borrow(byte, lf, 524288), fk: int fk): bool

implement template_matches (tb, tk, fb, fk) = _walk(tb, tk, 0, fb, fk, 0)
