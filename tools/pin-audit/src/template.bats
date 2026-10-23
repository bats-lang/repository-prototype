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

fun _walk {template_loc,file_loc:agz}{template_len,file_len:nat | template_len <= 524288; file_len <= 524288}{template_at:nat | template_at <= template_len}{file_at:nat | file_at <= file_len} .<template_len - template_at>.
  (template_text: !$A.borrow(byte, template_loc, 524288), template_len: int template_len, template_at: int template_at,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len, file_at: int file_at): bool =
  if template_at >= template_len then file_at >= file_len
  else let
    val commit = lit_step(template_text, template_len, template_at, "@@COMMIT@@")
  in
    if commit >= 0 then let
      val hex_end = hex_step(file_text, file_len, file_at, 40)
    in if hex_end >= 0 then _walk(template_text, template_len, commit, file_text, file_len, hex_end) else false end
    else let
      val comment = lit_step(template_text, template_len, template_at, "@@COMMENT@@")
    in
      if comment >= 0 then let
        val comment_end = class_end(file_text, file_len, file_at, Class_printable())
      in if comment_end > file_at then _walk(template_text, template_len, comment, file_text, file_len, comment_end) else false end
      else let
        val minute = lit_step(template_text, template_len, template_at, "@@MINUTE@@")
      in
        if minute >= 0 then let
          val digit_count = digits_upto_two(file_text, file_len, file_at)
        in if digit_count >= 1 then _walk(template_text, template_len, minute, file_text, file_len, file_at + digit_count) else false end
        else if file_at >= file_len then false
        else if byte2int0($A.read<byte>(template_text, template_at)) = byte2int0($A.read<byte>(file_text, file_at)) then _walk(template_text, template_len, template_at + 1, file_text, file_len, file_at + 1)
        else false
      end
    end
  end

(* Whether the file file_text[0, file_len) is the template template_text[0, template_len) with its holes filled *)
#pub fn template_matches {template_loc,file_loc:agz}{template_len,file_len:nat | template_len <= 524288; file_len <= 524288}
  (template_text: !$A.borrow(byte, template_loc, 524288), template_len: int template_len,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len): bool

implement template_matches (template_text, template_len, file_text, file_len) = _walk(template_text, template_len, 0, file_text, file_len, 0)
