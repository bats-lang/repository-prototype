(* ticket -- the one ticket of a diverging repository
   (bats-lang/repository-prototype#405). Keyword: pin-audit ticket.

   A repository with a file that is neither listed by hash nor equal to a
   template gets one ticket titled `Make <repository>'s workflow and
   issue-template files canonical`, labelled p0. Its body has, for each
   offending file, the file's path and the template of the same name with
   its holes filled: the commit is the commit of the repository-prototype
   checkout the audit runs in, the comment is `repository-prototype main `
   and the first 7 digits of that commit (the form the relock writes), the
   minute is the one the repository's current file has after the template's
   own text up to the hole (17 when the file does not have it). The last
   line is the Done-when. The audit opens no pull request. A ticket with the
   same title that is open is edited (its body replaced) and nothing is
   created. The template is read as bytes and its holes are found as text:
   nothing here reads YAML.

   Bounds: a repository name and a path are at most 255 bytes, a text at
   most 524288 bytes (the body of a ticket is a rope and not cut). *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use list as L
#use process as P

staload "support.sats"

(* ============================================================
   Finding the minute in the repository's current file
   ============================================================ *)

(* The start of the line of template_text[0, template_len) that holds the place at *)
fun _line_start {l:agz}{n:pos}{template_len:nat | template_len <= n}{at:nat | at <= template_len} .<at>.
  (template_text: !$A.borrow(byte, l, n), template_len: int template_len, at: int at): [start:nat | start <= at] int start =
  if at <= 0 then 0
  else if byte2int0($A.read<byte>(template_text, at - 1)) = 10 then at
  else _line_start(template_text, template_len, at - 1)

(* The first place at or after at of template_text[0, template_len) where the minute hole begins, or ~1 *)
fun _hole_at {l:agz}{n:pos}{template_len:nat | template_len <= n}{at:nat | at <= template_len} .<template_len - at>.
  (template_text: !$A.borrow(byte, l, n), template_len: int template_len, at: int at): [hole:int | hole < 0 || (hole >= at && hole <= template_len)] int hole =
  if at >= template_len then ~1
  else if lit_step(template_text, template_len, at, "@@MINUTE@@") >= 0 then at
  else _hole_at(template_text, template_len, at + 1)

(* The first place p at or after from of file_text[0, file_len) that holds
   template_text[prefix_start, hole) and then a digit: the place of the
   digits (at most two) and how many; none is a count of 0 *)
fun _find_minute {template_loc,file_loc:agz}{file_len:nat | file_len <= 524288}{prefix_start,hole:nat | prefix_start <= hole; hole <= 524288}{from:nat | from <= file_len} .<file_len - from>.
  (template_text: !$A.borrow(byte, template_loc, 524288), prefix_start: int prefix_start, hole: int hole,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len, from: int from)
  : [digits_start,digit_count:nat | digit_count <= 2; digits_start + digit_count <= file_len] @(int digits_start, int digit_count) =
  if from >= file_len then @(0, 0)
  else let
    val digits_at = from + (hole - prefix_start)
  in
    if digits_at > file_len then @(0, 0)
    else if range_eq(template_text, prefix_start, hole, file_text, from) then let
      val counted = digits_upto_two(file_text, file_len, digits_at)
    in
      if counted >= 1 then @(digits_at, counted)
      else _find_minute(template_text, prefix_start, hole, file_text, file_len, from + 1)
    end
    else _find_minute(template_text, prefix_start, hole, file_text, file_len, from + 1)
  end

(* The place and the count (at most two) of the digits the file file_text[0, file_len) has for the template's first minute hole; a count of 0 when it has none *)
fn _minute_of {template_loc,file_loc:agz}{template_len,file_len:nat | template_len <= 524288; file_len <= 524288}
  (template_text: !$A.borrow(byte, template_loc, 524288), template_len: int template_len,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len, file_whole: bool)
  : [digits_start,digit_count:nat | digit_count <= 2; digits_start + digit_count <= file_len] @(int digits_start, int digit_count) = let
  val hole = _hole_at(template_text, template_len, 0)
in
  if ~file_whole then @(0, 0)
  else if hole < 0 then @(0, 0)
  else let
    val prefix_start = _line_start(template_text, template_len, hole)
  in _find_minute(template_text, prefix_start, hole, file_text, file_len, 0) end
end

(* ============================================================
   Filling a template
   ============================================================ *)

(* template_text[at, template_len) written to out with each hole replaced by its value *)
fun _fill {template_loc,commit_loc,comment_loc,minute_loc:agz}{template_len,commit_len,comment_len,minute_start,minute_stop:nat | template_len <= 524288; commit_len <= 524288; comment_len <= 524288; minute_start <= minute_stop; minute_stop <= 524288}{at:nat | at <= template_len} .<template_len - at>.
  (template_text: !$A.borrow(byte, template_loc, 524288), template_len: int template_len, at: int at, out: !$B.sized_rope,
   commit_text: !$A.borrow(byte, commit_loc, 524288), commit_len: int commit_len,
   comment_text: !$A.borrow(byte, comment_loc, 524288), comment_len: int comment_len,
   minute_text: !$A.borrow(byte, minute_loc, 524288), minute_start: int minute_start, minute_stop: int minute_stop): void =
  if at >= template_len then ()
  else let
    val commit_end = lit_step(template_text, template_len, at, "@@COMMIT@@")
  in
    if commit_end >= 0 then let
      val () = $B.sized_rope_copy(out, commit_text, 0, commit_len)
    in _fill(template_text, template_len, commit_end, out, commit_text, commit_len, comment_text, comment_len, minute_text, minute_start, minute_stop) end
    else let
      val comment_end = lit_step(template_text, template_len, at, "@@COMMENT@@")
    in
      if comment_end >= 0 then let
        val () = $B.sized_rope_copy(out, comment_text, 0, comment_len)
      in _fill(template_text, template_len, comment_end, out, commit_text, commit_len, comment_text, comment_len, minute_text, minute_start, minute_stop) end
      else let
        val minute_end = lit_step(template_text, template_len, at, "@@MINUTE@@")
      in
        if minute_end >= 0 then let
          val () = $B.sized_rope_copy(out, minute_text, minute_start, minute_stop)
        in _fill(template_text, template_len, minute_end, out, commit_text, commit_len, comment_text, comment_len, minute_text, minute_start, minute_stop) end
        else let
          val () = $B.sized_rope_put(out, $AR.low_byte(byte2int0($A.read<byte>(template_text, at))))
        in _fill(template_text, template_len, at + 1, out, commit_text, commit_len, comment_text, comment_len, minute_text, minute_start, minute_stop) end
      end
    end
  end

(* ============================================================
   One offending file
   ============================================================ *)

(* The start of the last name of path_text[start, stop): after its last slash *)
fun _name_start {l:agz}{n:pos}{start,stop:nat | start <= stop; stop <= n}{from:nat | start <= from; from <= stop}{found:int} .<stop - from>.
  (path_text: !$A.borrow(byte, l, n), start: int start, stop: int stop, from: int from, found: int found): [name_start:nat | start <= name_start; name_start <= stop] int name_start = let
  val slash = find_byte(path_text, stop, from, 47)
in
  if slash >= stop then (if found < start then start else if found > stop then start else found)
  else _name_start(path_text, start, stop, slash + 1, slash + 1)
end

(* The template of the name of the file, filled, as a section of the body: the file is the path
   offenders_text[path_start, path_stop) of the clone of repository_text[repository_start, repository_stop), its sha256
   offenders_text[hash_start, hash_stop) *)
fn _section {repository_loc,offenders_loc,commit_loc,comment_loc:agz}{repository_start,repository_stop,path_start,path_stop,hash_start,hash_stop,commit_len,comment_len:nat | repository_start <= repository_stop; repository_stop - repository_start <= 255; repository_stop <= 524288; path_start <= path_stop; path_stop - path_start <= 255; path_stop <= 524288; hash_start <= hash_stop; hash_stop <= 524288; commit_len <= 524288; comment_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_stop: int repository_stop,
   offenders_text: !$A.borrow(byte, offenders_loc, 524288), path_start: int path_start, path_stop: int path_stop, hash_start: int hash_start, hash_stop: int hash_stop,
   commit_text: !$A.borrow(byte, commit_loc, 524288), commit_len: int commit_len,
   comment_text: !$A.borrow(byte, comment_loc, 524288), comment_len: int comment_len,
   body: !$B.sized_rope): void = let
  val () = $B.sized_rope_bput(body, "## `")
  val () = $B.sized_rope_copy(body, offenders_text, path_start, path_stop)
  val () = $B.sized_rope_bput(body, "`\n\n")
  val name_start = _name_start(offenders_text, path_start, path_stop, path_start, ~1)
  var template_path : $B.builder(0) = $B.create()
  val () = $B.bput(template_path, "tools/pin-audit/templates/")
  val () = put_range(offenders_text, name_start, path_stop, template_path)
  val @(template_path_array, template_path_len) = $B.to_arr(template_path)
  val @(template_path_frozen, template_path_view) = $A.freeze<byte>(template_path_array)
  var template : $B.builder(0) = $B.create()
  val @(template_ended, _) = read_file(template_path_view, template_path_len, template)
  val () = $A.drop<byte>(template_path_frozen, template_path_view)
  val () = $A.free<byte>($A.thaw<byte>(template_path_frozen))
  val @(template_array, template_len) = $B.to_arr(template)
  val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
  val () =
    (case+ template_ended of
     | Read_whole() => let
         var file_path : $B.builder(0) = $B.create()
         val () = $B.bput(file_path, "audit-clones/")
         val () = put_range(repository_text, repository_start, repository_stop, file_path)
         val () = $B.bput(file_path, "/")
         val () = put_range(offenders_text, path_start, path_stop, file_path)
         val @(file_path_array, file_path_len) = $B.to_arr(file_path)
         val @(file_path_frozen, file_path_view) = $A.freeze<byte>(file_path_array)
         var file : $B.builder(0) = $B.create()
         val @(file_ended, _) = read_file(file_path_view, file_path_len, file)
         val () = $A.drop<byte>(file_path_frozen, file_path_view)
         val () = $A.free<byte>($A.thaw<byte>(file_path_frozen))
         val @(file_array, file_len) = $B.to_arr(file)
         val @(file_frozen, file_view) = $A.freeze<byte>(file_array)
         val file_whole = (case+ file_ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
         val @(digits_start, digit_count) = _minute_of(template_view, template_len, file_view, file_len, file_whole)
         val () = $B.sized_rope_bput(body, "The audit compares bytes: the file is exactly this text.\n\n```\n")
         val () =
           if digit_count >= 1 then
             _fill(template_view, template_len, 0, body, commit_text, commit_len, comment_text, comment_len, file_view, digits_start, digits_start + digit_count)
           else let
             var seventeen : $B.builder(0) = $B.create()
             val () = $B.bput(seventeen, "17")
             val @(seventeen_array, seventeen_len) = $B.to_arr(seventeen)
             val @(seventeen_frozen, seventeen_view) = $A.freeze<byte>(seventeen_array)
             val () = _fill(template_view, template_len, 0, body, commit_text, commit_len, comment_text, comment_len, seventeen_view, 0, seventeen_len)
             val () = $A.drop<byte>(seventeen_frozen, seventeen_view)
             val () = $A.free<byte>($A.thaw<byte>(seventeen_frozen))
           in () end
         val () = $B.sized_rope_bput(body, "```\n\n")
         val () = $A.drop<byte>(file_frozen, file_view)
         val () = $A.free<byte>($A.thaw<byte>(file_frozen))
       in () end
     | Read_too_long() => $B.sized_rope_bput(body, "The template of this name is longer than the 524288 bytes the audit reads.\n\n")
     | Read_failed() => let
         val () = $B.sized_rope_bput(body, "No template of this name is in tools/pin-audit/templates of bats-lang/repository-prototype, so the file has no correct text to show. Delete it")
       in
         if hash_stop - hash_start = 64 then let
           val () = $B.sized_rope_bput(body, ", or list its sha256 ")
           val () = $B.sized_rope_copy(body, offenders_text, hash_start, hash_stop)
         in $B.sized_rope_bput(body, " in tools/pin-audit/allowlist.txt there with a ticket comment.\n\n") end
         else $B.sized_rope_bput(body, ".\n\n")
       end)
  val () = $A.drop<byte>(template_frozen, template_view)
  val () = $A.free<byte>($A.thaw<byte>(template_frozen))
in () end

(* The sections of the lines of offenders_text[0, offenders_len) from at, each `<path><tab><sha256>` and a newline *)
fun _sections {repository_loc,offenders_loc,commit_loc,comment_loc:agz}{repository_start,repository_stop,offenders_len,commit_len,comment_len:nat | repository_start <= repository_stop; repository_stop - repository_start <= 255; repository_stop <= 524288; offenders_len <= 524288; commit_len <= 524288; comment_len <= 524288}{at:nat | at <= offenders_len} .<offenders_len - at>.
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_stop: int repository_stop,
   offenders_text: !$A.borrow(byte, offenders_loc, 524288), offenders_len: int offenders_len, at: int at,
   commit_text: !$A.borrow(byte, commit_loc, 524288), commit_len: int commit_len,
   comment_text: !$A.borrow(byte, comment_loc, 524288), comment_len: int comment_len,
   body: !$B.sized_rope): void = let
  val line_stop = line_end(offenders_text, offenders_len, at)
  val tab = find_byte(offenders_text, line_stop, at, 9)
  val () =
    if tab >= line_stop then ()
    else if tab - at > 255 then ()
    else _section(repository_text, repository_start, repository_stop, offenders_text, at, tab, tab + 1, line_stop, commit_text, commit_len, comment_text, comment_len, body)
in
  if line_stop >= offenders_len then ()
  else _sections(repository_text, repository_start, repository_stop, offenders_text, offenders_len, line_stop + 1, commit_text, commit_len, comment_text, comment_len, body)
end

(* ============================================================
   The ticket
   ============================================================ *)

(* The arguments of `gh issue list` for the open tickets of the repository whose title is the exact title, printing their numbers *)
fn _list_argv {repository_loc:agz}{repository_start,repository_stop:nat | repository_start <= repository_stop; repository_stop - repository_start <= 255; repository_stop <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_stop: int repository_stop): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("gh"),
  $L.list_vt_cons(arg_text("issue"),
  $L.list_vt_cons(arg_text("list"),
  $L.list_vt_cons(arg_text("-R"),
  $L.list_vt_cons(arg_range("bats-lang/", repository_text, repository_start, repository_stop, ""),
  $L.list_vt_cons(arg_text("--state"),
  $L.list_vt_cons(arg_text("open"),
  $L.list_vt_cons(arg_text("--limit"),
  $L.list_vt_cons(arg_text("100"),
  $L.list_vt_cons(arg_text("--search"),
  $L.list_vt_cons(arg_range("Make ", repository_text, repository_start, repository_stop, "'s workflow and issue-template files canonical in:title"),
  $L.list_vt_cons(arg_text("--json"),
  $L.list_vt_cons(arg_text("number,title"),
  $L.list_vt_cons(arg_text("--jq"),
  $L.list_vt_cons(arg_range(".[] | select(.title == \"Make ", repository_text, repository_start, repository_stop, "'s workflow and issue-template files canonical\") | .number"),
    $L.list_vt_nil())))))))))))))))

(* gh with the arguments, its output printed after the label: the status *)
fn _gh_print {label_len:nat | label_len <= 100} (argv: $L.listv($P.arg_entry), label: string label_len): int = let
  var out : $B.builder(0) = $B.create()
  val @(status, _) = capture_with("gh", argv, no_arguments(), out)
  val @(out_array, out_len) = $B.to_arr(out)
  val @(out_frozen, out_view) = $A.freeze<byte>(out_array)
  val () = print! ("   ticket ", label, ": ")
  val () = print_range(out_view, 0, out_len)
  val () = if out_len = 0 then println!() else ()
  val () = $A.drop<byte>(out_frozen, out_view)
  val () = $A.free<byte>($A.thaw<byte>(out_frozen))
in status end

(* Files the ticket of the repository repository_text[repository_start, repository_stop) for the offending files
   offenders_text[0, offenders_len) (lines `<path><tab><sha256>`), with the commit commit_text[0, 40) of the
   checkout the audit runs in: an open ticket of the title is edited, else one is created. Whether it was. *)
#pub fn file_ticket {repository_loc,offenders_loc,commit_loc:agz}{repository_start,repository_stop,offenders_len:nat | repository_start <= repository_stop; repository_stop - repository_start <= 255; repository_stop <= 524288; offenders_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_stop: int repository_stop,
   offenders_text: !$A.borrow(byte, offenders_loc, 524288), offenders_len: int offenders_len,
   commit_text: !$A.borrow(byte, commit_loc, 524288)): bool

implement file_ticket (repository_text, repository_start, repository_stop, offenders_text, offenders_len, commit_text) = let
  var comment : $B.builder(0) = $B.create()
  val () = $B.bput(comment, "repository-prototype main ")
  val () = put_range(commit_text, 0, 7, comment)
  val @(comment_array, comment_len) = $B.to_arr(comment)
  val @(comment_frozen, comment_view) = $A.freeze<byte>(comment_array)
  var body : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(body, "These workflow files are neither listed by sha256 in tools/pin-audit/allowlist.txt of bats-lang/repository-prototype nor equal to a template there with its holes filled. The correct file is shown for each.\n\n")
  val () = _sections(repository_text, repository_start, repository_stop, offenders_text, offenders_len, 0, commit_text, 40, comment_view, comment_len, body)
  val () = $B.sized_rope_bput(body, "Done when: `pin_audit --repository ")
  val () = $B.sized_rope_copy(body, repository_text, repository_start, repository_stop)
  val () = $B.sized_rope_bput(body, "` exits 0.\n")
  val () = $A.drop<byte>(comment_frozen, comment_view)
  val () = $A.free<byte>($A.thaw<byte>(comment_frozen))
  var body_path : $B.builder(0) = $B.create()
  val () = $B.bput(body_path, "audit-clones/")
  val () = put_range(repository_text, repository_start, repository_stop, body_path)
  val () = $B.bput(body_path, ".ticket.md")
  val @(body_path_array, body_path_len) = $B.to_arr(body_path)
in
  if write_rope(@(body_path_array, body_path_len), body) then let
    val @(listed_status, listed_ended) = let
      var listed : $B.builder(0) = $B.create()
      val @(status, ended) = capture_with("gh", _list_argv(repository_text, repository_start, repository_stop), no_arguments(), listed)
      val @(listed_array, listed_len) = $B.to_arr(listed)
      val @(listed_frozen, listed_view) = $A.freeze<byte>(listed_array)
      val number_stop = class_end(listed_view, listed_len, 0, Class_digit())
      val edit_status =
        (if status = 0 && number_stop > 0 then
           _gh_print($L.list_vt_cons(arg_text("gh"),
             $L.list_vt_cons(arg_text("issue"),
             $L.list_vt_cons(arg_text("edit"),
             $L.list_vt_cons(arg_range("", listed_view, 0, number_stop, ""),
             $L.list_vt_cons(arg_text("-R"),
             $L.list_vt_cons(arg_range("bats-lang/", repository_text, repository_start, repository_stop, ""),
             $L.list_vt_cons(arg_text("--body-file"),
             $L.list_vt_cons(arg_range("audit-clones/", repository_text, repository_start, repository_stop, ".ticket.md"),
               $L.list_vt_nil())))))))), "updated")
         else if status = 0 then
           _gh_print($L.list_vt_cons(arg_text("gh"),
             $L.list_vt_cons(arg_text("issue"),
             $L.list_vt_cons(arg_text("create"),
             $L.list_vt_cons(arg_text("-R"),
             $L.list_vt_cons(arg_range("bats-lang/", repository_text, repository_start, repository_stop, ""),
             $L.list_vt_cons(arg_text("--title"),
             $L.list_vt_cons(arg_range("Make ", repository_text, repository_start, repository_stop, "'s workflow and issue-template files canonical"),
             $L.list_vt_cons(arg_text("--label"),
             $L.list_vt_cons(arg_text("p0"),
             $L.list_vt_cons(arg_text("--body-file"),
             $L.list_vt_cons(arg_range("audit-clones/", repository_text, repository_start, repository_stop, ".ticket.md"),
               $L.list_vt_nil()))))))))))), "created")
         else status): int
      val () = $A.drop<byte>(listed_frozen, listed_view)
      val () = $A.free<byte>($A.thaw<byte>(listed_frozen))
    in @(edit_status, ended) end
    val () =
      if listed_status = 0 then ()
      else let
        val () = print! ("::error title=pin audit::")
        val () = print_range(repository_text, repository_start, repository_stop)
      in println! (": gh could not list, edit or create the ticket (status ", listed_status, ")") end
    val () = (case+ listed_ended of | Read_whole() => () | Read_too_long() => () | Read_failed() => ())
  in listed_status = 0 end
  else let
    val () = print! ("::error title=pin audit::")
    val () = print_range(repository_text, repository_start, repository_stop)
    val () = println! (": the ticket's body could not be written")
  in false end
end
