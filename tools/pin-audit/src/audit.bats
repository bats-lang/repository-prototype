(* audit -- every workflow file of every non-archived repository of the
   organisation is allowlisted by its hash or equals a template
   (bats-lang/repository-prototype#396). Keyword: pin-audit.

   A workflow file passes when exactly one holds, and is "not canonical"
   otherwise: its sha256 is listed with its repository and path in
   tools/pin-audit/allowlist.txt (allowlist.bats), or its bytes are a
   template of tools/pin-audit/templates with the holes filled
   (template.bats). No line rule, no per-job rule, no YAML.

   Bounds: a text is at most 524288 bytes (a file over it is a failure of
   its own, said and counted, never cut), a repository name and a path at
   most 255 bytes. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use file as F
#use list as L
#use process as P
#use result as R

staload "support.sats"
staload "allowlist.sats"
staload "template.sats"

(* ============================================================
   Constant paths
   ============================================================ *)

(* ============================================================
   The templates: every *.yml of tools/pin-audit/templates
   ============================================================ *)

(* What one template was: it could not be read whole, it was read and the
   file is not it, it was read and the file is it. Every caller matches all
   three (case+). *)
datatype template_result =
  | Template_unreadable
  | Template_other
  | Template_equal

(* The template whose file name is template_name_view[0, template_name_len) (at most 255 bytes) against
   the file file_text[0, file_len); with report it says what it found *)
fn _try_template {template_name_loc,file_loc:agz}{template_name_len:nat | template_name_len <= 255}{file_len:nat | file_len <= 524288}
  (template_name_view: !$A.borrow(byte, template_name_loc, 1024), template_name_len: int template_name_len,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len, report: bool): template_result = let
  var path_builder : $B.builder(0) = $B.create()
  val () = $B.bput(path_builder, "tools/pin-audit/templates/")
  val () = put_range(template_name_view, 0, template_name_len, path_builder)
  val @(path_array, path_len) = $B.to_arr(path_builder)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var content : $B.builder(0) = $B.create()
  val @(ended, why) = read_file(path_view, path_len, content)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val @(content_array, content_len) = $B.to_arr(content)
  val @(content_frozen, content_view) = $A.freeze<byte>(content_array)
  val result =
    (case+ ended of
     | Read_whole() => let
         val () =
           if report then let
             val () = print! ("   template ")
             val () = print_range(template_name_view, 0, template_name_len)
           in println! (": read, ", content_len, " bytes") end
           else ()
       in
         if template_matches(content_view, content_len, file_text, file_len) then Template_equal() else Template_other()
       end
     | Read_too_long() => let
         val () = print! ("::error title=pin audit::template ")
         val () = print_range(template_name_view, 0, template_name_len)
       in (println! (" is longer than the 524288 bytes the audit reads"); Template_unreadable()) end
     | Read_failed() => let
         val () = print! ("::error title=pin audit::template ")
         val () = print_range(template_name_view, 0, template_name_len)
       in (println! (" could not be read: ", why); Template_unreadable()) end): template_result
  val () = $A.drop<byte>(content_frozen, content_view)
  val () = $A.free<byte>($A.thaw<byte>(content_frozen))
in result end

(* Entry i and after of the templates directory: the length of the name of
   the first template the file file_text[0, file_len) is (copied to name_out), else 0,
   with how many templates were read and how many could not be. With
   report, no template is looked for: every one is read and said. *)
fun _scan {n:nat}{i:nat | i <= n}{file_loc,out_loc:agz}{file_len:nat | file_len <= 524288} .<n - i>.
  (entries: !$F.entries(n), n: int n, i: int i,
   file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len,
   name_out: !$A.arr(byte, out_loc, 256), report: bool, loaded: int, bad: int)
  : @([found_len:nat | found_len <= 255] int found_len, int, int) =
  if i >= n then @(0, loaded, bad)
  else let
    val name_buffer = $A.alloc<byte>(1024)
    val name_len = $F.entries_name(entries, i, name_buffer, 1024)
    val @(name_frozen, name_view) = $A.freeze<byte>(name_buffer)
    val yml = (if name_len >= 5 then lit_step(name_view, name_len, name_len - 4, ".yml") >= 0 else false): bool
    val @(found, loaded2, bad2) =
      (if ~yml then @(0, loaded, bad)
       else if name_len > 255 then let
         val () = print! ("::error title=pin audit::a template name of ", name_len, " bytes is longer than the 255 the audit will put in a path")
         val () = println! ()
       in @(0, loaded, bad + 1) end
       else
         (case+ _try_template(name_view, name_len, file_text, file_len, report) of
          | Template_unreadable() => @(0, loaded, bad + 1)
          | Template_other() => @(0, loaded + 1, bad)
          | Template_equal() =>
              if report then @(0, loaded + 1, bad)
              else let val () = copy_into(name_view, name_len, name_out) in @(name_len, loaded + 1, bad) end)): @([found_len:nat | found_len <= 255] int found_len, int, int)
    val () = $A.drop<byte>(name_frozen, name_view)
    val () = $A.free<byte>($A.thaw<byte>(name_frozen))
  in
    if found > 0 then @(found, loaded2, bad2)
    else _scan(entries, n, i + 1, file_text, file_len, name_out, report, loaded2, bad2)
  end

(* The name of the template the file file_text[0, file_len) is, in name_out[0, result),
   or 0 when it is none *)
fn _template_of {file_loc,out_loc:agz}{file_len:nat | file_len <= 524288}
  (file_text: !$A.borrow(byte, file_loc, 524288), file_len: int file_len, name_out: !$A.arr(byte, out_loc, 256))
  : [found_len:nat | found_len <= 255] int found_len = let
  var path_builder : $B.builder(0) = $B.create()
  val () = $B.bput(path_builder, "tools/pin-audit/templates")
  val @(path_array, path_len) = $B.to_arr(path_builder)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val listed = dir_entries(path_view, path_len)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in
  case+ listed of
  | ~$R.err(_) => 0
  | ~$R.ok(entries) => let
      val @(found, _, _) = _scan(entries, $F.entries_count(entries), 0, file_text, file_len, name_out, false, 0, 0)
      val () = $F.entries_free(entries)
    in found end
end

(* Reads every template once and says each: how many were read and how many
   could not be (a missing directory counts as one) *)
fn _templates_check (): @(int, int) = let
  var path_builder : $B.builder(0) = $B.create()
  val () = $B.bput(path_builder, "tools/pin-audit/templates")
  val @(path_array, path_len) = $B.to_arr(path_builder)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val listed = dir_entries(path_view, path_len)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val empty = $A.alloc<byte>(524288)
  val @(empty_frozen, empty_view) = $A.freeze<byte>(empty)
  val counts =
    (case+ listed of
     | ~$R.err(failure) => let
         val () = println! ("::error title=pin audit::the templates directory tools/pin-audit/templates could not be read: ", $F.io_error_text(failure))
       in @(0, 1) end
     | ~$R.ok(entries) => let
         val name_out = $A.alloc<byte>(256)
         val @(_, loaded, bad) = _scan(entries, $F.entries_count(entries), 0, empty_view, 0, name_out, true, 0, 0)
         val () = $A.free<byte>(name_out)
         val () = $F.entries_free(entries)
       in @(loaded, bad) end): @(int, int)
  val () = $A.drop<byte>(empty_frozen, empty_view)
  val () = $A.free<byte>($A.thaw<byte>(empty_frozen))
in counts end

(* ============================================================
   The counts
   ============================================================ *)

(* Workflow files, those passed by their hash, those passed by a template,
   those not canonical, those over the bound, those unreadable, and the
   failures of a repository itself (its name, its clone, its list of
   workflows) *)
typedef tally = @(int, int, int, int, int, int, int)

(* The column of the counts a file or a failure goes into: hashed, templated,
   not canonical, over the bound, unreadable; Column_repository is one more
   repository error and no file. Every caller matches all six (case+). *)
datatype column =
  | Column_hashed
  | Column_templated
  | Column_not_canonical
  | Column_over_bound
  | Column_unreadable
  | Column_repository

(* One more file in the column, or one more repository error *)
fn _bump (counts: tally, which: column): tally = let
  val @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors) = counts
in
  case+ which of
  | Column_hashed() => @(files + 1, hashed + 1, templated, not_canonical, over_bound, unreadable, repository_errors)
  | Column_templated() => @(files + 1, hashed, templated + 1, not_canonical, over_bound, unreadable, repository_errors)
  | Column_not_canonical() => @(files + 1, hashed, templated, not_canonical + 1, over_bound, unreadable, repository_errors)
  | Column_over_bound() => @(files + 1, hashed, templated, not_canonical, over_bound + 1, unreadable, repository_errors)
  | Column_unreadable() => @(files + 1, hashed, templated, not_canonical, over_bound, unreadable + 1, repository_errors)
  | Column_repository() => @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors + 1)
end

fn _failures (counts: tally): int = let
  val @(_, _, _, not_canonical, over_bound, unreadable, repository_errors) = counts
in not_canonical + over_bound + unreadable + repository_errors end

(* ============================================================
   One workflow file
   ============================================================ *)

(* The start of a file's failure line: the annotation, the repository, the
   path *)
fn _file_error {repository_loc,path_loc:agz}{repository_start,repository_end,path_start,path_end:nat | repository_start <= repository_end; repository_end <= 524288; path_start <= path_end; path_end <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end): void = let
  val () = print! ("::error title=pin audit::")
  val () = print_range(repository_text, repository_start, repository_end)
  val () = print! (": ")
  val () = print_range(path_text, path_start, path_end)
in print! (": ") end

(* The start of a file's passing line *)
fn _file_pass {path_loc:agz}{path_start,path_end:nat | path_start <= path_end; path_end <= 524288}
  (path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end): void = let
  val () = print! ("   ")
  val () = print_range(path_text, path_start, path_end)
in print! (": pass, ") end

(* The file whose bytes are content_text[0, content_len) and whose sha256 is hash_text[0, 64): its
   verdict is printed and its column returned *)
fn _verdict {repository_loc,path_loc,content_loc,hash_loc,allowlist_loc:agz}{repository_start,repository_end,path_start,path_end,content_len,allowlist_len:nat | repository_start <= repository_end; repository_end <= 524288; path_start <= path_end; path_end <= 524288; content_len <= 524288; allowlist_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end,
   content_text: !$A.borrow(byte, content_loc, 524288), content_len: int content_len,
   hash_text: !$A.borrow(byte, hash_loc, 64),
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len): column = let
  val @(slot, line_number) = allowlist_find(allowlist_text, allowlist_len, repository_text, repository_start, repository_end, path_text, path_start, path_end, hash_text)
  val name_out = $A.alloc<byte>(256)
  val named = _template_of(content_text, content_len, name_out)
  val @(template_name_frozen, template_name_view) = $A.freeze<byte>(name_out)
  val listed = (case+ slot of | Hash_current() => true | Hash_next() => true | Hash_unlisted() => false): bool
  val verdict_column =
    (if listed && named = 0 then let
       val () = _file_pass(path_text, path_start, path_end)
       val () = print! ("its sha256 is the ")
       val () =
         (case+ slot of
          | Hash_current() => print! ("current")
          | Hash_next() => print! ("next")
          | Hash_unlisted() => print! ("unlisted"))
       val () = print! (" hash of tools/pin-audit/allowlist.txt line ", line_number)
     in (println! (); Column_hashed()) end
     else if ~listed && named > 0 then let
       val () = _file_pass(path_text, path_start, path_end)
       val () = print! ("equal to the template ")
       val () = print_range(template_name_view, 0, named)
     in (println! (" with its holes filled"); Column_templated()) end
     else if listed then let
       val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
       val () = print! ("not canonical: its sha256 is listed in tools/pin-audit/allowlist.txt line ", line_number, " and it equals the template ")
       val () = print_range(template_name_view, 0, named)
     in (println! ("; exactly one may hold: drop the allowlist entry"); Column_not_canonical()) end
     else let
       val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
       val () = print! ("not canonical: its sha256 ")
       val () = print_range(hash_text, 0, 64)
     in (println! (" is not listed for it in tools/pin-audit/allowlist.txt and it equals no template with its holes filled"); Column_not_canonical()) end): column
  val () = $A.drop<byte>(template_name_frozen, template_name_view)
  val () = $A.free<byte>($A.thaw<byte>(template_name_frozen))
in verdict_column end

(* The file path_text[path_start, path_end) of the clone of repository_text[repository_start, repository_end), at most 255 bytes of path
   and of name: read (at most 524288 bytes), hashed and judged *)
fn _audit_file_in {repository_loc,path_loc,allowlist_loc:agz}{repository_start,repository_end,path_start,path_end,allowlist_len:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288; path_start <= path_end; path_end - path_start <= 255; path_end <= 524288; allowlist_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end,
   symlink: bool, allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, counts: tally): tally =
  if symlink then let
    val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
    val () = println! ("not canonical: it is a symbolic link (git mode 120000), which no template or hash describes")
  in _bump(counts, Column_not_canonical()) end
  else let
    var clone_path : $B.builder(0) = $B.create()
    val () = $B.bput(clone_path, "audit-clones/")
    val () = put_range(repository_text, repository_start, repository_end, clone_path)
    val () = $B.bput(clone_path, "/")
    val () = put_range(path_text, path_start, path_end, clone_path)
    val @(clone_array, clone_len) = $B.to_arr(clone_path)
    val @(clone_frozen, clone_view) = $A.freeze<byte>(clone_array)
    var content : $B.builder(0) = $B.create()
    val @(ended, why) = read_file(clone_view, clone_len, content)
    val () = $A.drop<byte>(clone_frozen, clone_view)
    val () = $A.free<byte>($A.thaw<byte>(clone_frozen))
    val @(content_array, content_len) = $B.to_arr(content)
  in
    case+ ended of
    | Read_whole() => let
        val hex = sha256_hex(content_array, content_len)
        val @(hash_frozen, hash_view) = $A.freeze<byte>(hex)
        val @(content_frozen, content_view) = $A.freeze<byte>(content_array)
        val file_column = _verdict(repository_text, repository_start, repository_end, path_text, path_start, path_end, content_view, content_len, hash_view, allowlist_text, allowlist_len)
        val () = $A.drop<byte>(content_frozen, content_view)
        val () = $A.free<byte>($A.thaw<byte>(content_frozen))
        val () = $A.drop<byte>(hash_frozen, hash_view)
        val () = $A.free<byte>($A.thaw<byte>(hash_frozen))
      in _bump(counts, file_column) end
    | Read_too_long() => let
        val () = $A.free<byte>(content_array)
        val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
        val () = println! ("over the bound: the file is longer than the 524288 bytes the audit reads, so it is not compared")
      in _bump(counts, Column_over_bound()) end
    | Read_failed() => let
        val () = $A.free<byte>(content_array)
        val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
        val () = println! ("unreadable: ", why)
      in _bump(counts, Column_unreadable()) end
  end

(* The workflow file path_text[path_start, path_end) of the repository repository_text[repository_start, repository_end) *)
fn _audit_file {repository_loc,path_loc,allowlist_loc:agz}{repository_start,repository_end,path_start,path_end,allowlist_len:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288; path_start <= path_end; path_end <= 524288; allowlist_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   path_text: !$A.borrow(byte, path_loc, 524288), path_start: int path_start, path_end: int path_end,
   symlink: bool, allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, counts: tally): tally =
  if path_end - path_start > 255 then let
    val () = _file_error(repository_text, repository_start, repository_end, path_text, path_start, path_end)
    val () = println! ("over the bound: its path is ", path_end - path_start, " bytes, longer than the 255 the audit will put in a path")
  in _bump(counts, Column_over_bound()) end
  else _audit_file_in(repository_text, repository_start, repository_end, path_text, path_start, path_end, symlink, allowlist_text, allowlist_len, counts)

(* ============================================================
   One repository
   ============================================================ *)

(* Whether repository_text[repository_start, repository_end) is a name the clone's path can hold: letters, digits,
   '.', '_' and '-', and not "." or "..". It goes into arguments, never a
   shell, and into audit-clones/<name>. *)
fn _name_ok {repository_loc:agz}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): bool =
  if repository_end <= repository_start then false
  else if class_end(repository_text, repository_end, repository_start, Class_name()) < repository_end then false
  else if line_is(repository_text, repository_start, repository_end, ".") then false
  else if line_is(repository_text, repository_start, repository_end, "..") then false
  else true

(* The annotation that names the repository, ready for its message *)
fn _repository_error {repository_loc:agz}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): void = let
  val () = print! ("::error title=pin audit::")
  val () = print_range(repository_text, repository_start, repository_end)
in print! (": ") end

fn _clone_argv {repository_loc:agz}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("git"),
  $L.list_vt_cons(arg_text("clone"),
  $L.list_vt_cons(arg_text("--quiet"),
  $L.list_vt_cons(arg_text("--depth"),
  $L.list_vt_cons(arg_text("1"),
  $L.list_vt_cons(arg_text("--"),
  $L.list_vt_cons(arg_range("https://github.com/bats-lang/", repository_text, repository_start, repository_end, ".git"),
  $L.list_vt_cons(arg_range("audit-clones/", repository_text, repository_start, repository_end, ""),
    $L.list_vt_nil()))))))))

(* The records of the listing of .github/workflows in the clone *)
fn _tree_argv {repository_loc:agz}{repository_start,repository_end:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("git"),
  $L.list_vt_cons(arg_text("-C"),
  $L.list_vt_cons(arg_range("audit-clones/", repository_text, repository_start, repository_end, ""),
  $L.list_vt_cons(arg_text("ls-tree"),
  $L.list_vt_cons(arg_text("-z"),
  $L.list_vt_cons(arg_text("HEAD"),
  $L.list_vt_cons(arg_text(".github/workflows/"),
    $L.list_vt_nil())))))))

(* Every record of listing_text[0, listing_len) from i, `<mode> <type> <object>\t<path>` and a
   zero byte (git ls-tree -z): a blob whose path ends in .yml or .yaml is a
   workflow file. A record not of that form is an error of the repository. *)
fun _records {repository_loc,listing_loc,allowlist_loc:agz}{repository_start,repository_end,listing_len,allowlist_len:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288; listing_len <= 524288; allowlist_len <= 524288}{i:nat | i <= listing_len} .<listing_len - i>.
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   listing_text: !$A.borrow(byte, listing_loc, 524288), listing_len: int listing_len, i: int i,
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, counts: tally): tally = let
  val j = find_byte(listing_text, listing_len, i, 0)
  val tab_at = find_byte(listing_text, j, i, 9)
  val first_space = find_byte(listing_text, tab_at, i, 32)
  val counts_after =
    (if j <= i then counts
     else if tab_at >= j then let
       val () = _repository_error(repository_text, repository_start, repository_end)
     in (println! ("a record of the workflow listing has no tab"); _bump(counts, Column_repository())) end
     else if first_space + 1 > tab_at then let
       val () = _repository_error(repository_text, repository_start, repository_end)
     in (println! ("a record of the workflow listing has no type"); _bump(counts, Column_repository())) end
     else let
       val second_space = find_byte(listing_text, tab_at, first_space + 1, 32)
       val blob = line_is(listing_text, first_space + 1, second_space, "blob")
       val path_at = tab_at + 1
       val yml = (if j - 4 >= path_at then lit_step(listing_text, j, j - 4, ".yml") >= 0 else false): bool
       val yaml = (if j - 5 >= path_at then lit_step(listing_text, j, j - 5, ".yaml") >= 0 else false): bool
     in
       if blob && (yml || yaml) then _audit_file(repository_text, repository_start, repository_end, listing_text, path_at, j, line_is(listing_text, i, first_space, "120000"), allowlist_text, allowlist_len, counts)
       else counts
     end): tally
in
  if j >= listing_len then counts_after else _records(repository_text, repository_start, repository_end, listing_text, listing_len, j + 1, allowlist_text, allowlist_len, counts_after)
end

(* The clone of repository_text[repository_start, repository_end) and its files *)
fn _audit_clone {repository_loc,allowlist_loc:agz}{repository_start,repository_end,allowlist_len:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288; allowlist_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, counts: tally): tally = let
  var listing : $B.builder(0) = $B.create()
  val @(status, ended) = capture_with("git", _tree_argv(repository_text, repository_start, repository_end), no_arguments(), listing)
  val @(listing_array, listing_len) = $B.to_arr(listing)
  val @(listing_frozen, listing_view) = $A.freeze<byte>(listing_array)
  val counts_after =
    (case+ ended of
     | Read_whole() =>
         if status = 0 then _records(repository_text, repository_start, repository_end, listing_view, listing_len, 0, allowlist_text, allowlist_len, counts)
         else let
           val () = _repository_error(repository_text, repository_start, repository_end)
         in (println! ("git ls-tree could not list .github/workflows (status ", status, ")"); _bump(counts, Column_repository())) end
     | Read_too_long() => let
         val () = _repository_error(repository_text, repository_start, repository_end)
       in (println! ("over the bound: the list of workflow files is longer than the 524288 bytes the audit reads"); _bump(counts, Column_over_bound())) end
     | Read_failed() => let
         val () = _repository_error(repository_text, repository_start, repository_end)
       in (println! ("the list of workflow files could not be read"); _bump(counts, Column_repository())) end): tally
  val () = $A.drop<byte>(listing_frozen, listing_view)
  val () = $A.free<byte>($A.thaw<byte>(listing_frozen))
in counts_after end

(* Audits repository_text[repository_start, repository_end): its files counted into counts *)
fn _audit_one {repository_loc,allowlist_loc:agz}{repository_start,repository_end,allowlist_len:nat | repository_start <= repository_end; repository_end - repository_start <= 255; repository_end <= 524288; allowlist_len <= 524288}
  (repository_text: !$A.borrow(byte, repository_loc, 524288), repository_start: int repository_start, repository_end: int repository_end,
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len, counts: tally): tally =
  if ~_name_ok(repository_text, repository_start, repository_end) then let
    val () = _repository_error(repository_text, repository_start, repository_end)
  in (println! ("the repository's name is not one the audit will put in a path"); _bump(counts, Column_repository())) end
  else let
    val cloned = run_with("git", _clone_argv(repository_text, repository_start, repository_end), no_arguments())
  in
    if cloned != 0 then let
      val () = _repository_error(repository_text, repository_start, repository_end)
    in (println! ("cannot be cloned (git status ", cloned, ")"); _bump(counts, Column_repository())) end
    else let
      val @(files_before, _, _, _, _, _, _) = counts
      val counts_after = _audit_clone(repository_text, repository_start, repository_end, allowlist_text, allowlist_len, counts)
      val @(files_after, _, _, _, _, _, _) = counts_after
      val () = if files_after = files_before then println! ("   no workflow files") else ()
    in counts_after end
  end

(* The failing names, in order, to standard output *)
fun _print_chunks {n:nat} .<n>. (chunks: $B.rope_sized_list(n)): void =
  case+ chunks of
  | ~$B.rope_sized_nil() => ()
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(chunk_frozen, chunk_view) = $A.freeze<byte>(chunk)
      val () = print_range(chunk_view, 0, used)
      val () = $A.drop<byte>(chunk_frozen, chunk_view)
      val () = $A.free<byte>($A.thaw<byte>(chunk_frozen))
    in _print_chunks(rest) end

(* Every name in names_text[0, names_len) from i, one on each line: audited with the counts
   going on from counts, the failing ones going into failing. A name over 255
   bytes is a failure of its own, said and counted. *)
fun _audit_names {names_loc,allowlist_loc:agz}{names_len,allowlist_len:nat | names_len <= 524288; allowlist_len <= 524288}{i:nat | i <= names_len} .<names_len - i>.
  (names_text: !$A.borrow(byte, names_loc, 524288), names_len: int names_len, i: int i,
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len,
   failing: !$B.sized_rope, audited: int, counts: tally): @(int, tally) = let
  val j = line_end(names_text, names_len, i)
  val @(audited2, counts_after) =
    (if j <= i then @(audited, counts)
     else let
       val () = (print! ("== "); print_range(names_text, i, j); println! ())
       val before = _failures(counts)
       val counts_audited =
         (if j - i <= 255 then _audit_one(names_text, i, j, allowlist_text, allowlist_len, counts)
          else let
            val () = _repository_error(names_text, i, j)
          in (println! ("the repository's name is ", j - i, " bytes, longer than the 255 the audit will put in a path"); _bump(counts, Column_repository())) end): tally
       val () =
         if _failures(counts_audited) > before then let
           val () = $B.sized_rope_put(failing, 32)
         in $B.sized_rope_copy(failing, names_text, i, j) end
         else ()
     in @(audited + 1, counts_audited) end): @(int, tally)
in
  if j >= names_len then @(audited2, counts_after) else _audit_names(names_text, names_len, j + 1, allowlist_text, allowlist_len, failing, audited2, counts_after)
end

(* ============================================================
   The organisation
   ============================================================ *)

(* The organisation's non-archived repositories: gh's own jq keeps the names *)
fn _list_argv (): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("gh"),
  $L.list_vt_cons(arg_text("api"),
  $L.list_vt_cons(arg_text("--paginate"),
  $L.list_vt_cons(arg_text("orgs/bats-lang/repos"),
  $L.list_vt_cons(arg_text("--jq"),
  $L.list_vt_cons(arg_text(".[] | select(.archived == false) | .name"),
    $L.list_vt_nil()))))))

(* The audit of the names in names_text[0, names_len) with the allowlist allowlist_text[0, allowlist_len): the
   status of the run *)
fn _audit_all {names_loc,allowlist_loc:agz}{names_len,allowlist_len:nat | names_len <= 524288; allowlist_len <= 524288}
  (names_text: !$A.borrow(byte, names_loc, 524288), names_len: int names_len,
   allowlist_text: !$A.borrow(byte, allowlist_loc, 524288), allowlist_len: int allowlist_len,
   entries: int, bad_entries: int, templates: int, bad_templates: int): int = let
  var failing : $B.sized_rope = $B.sized_rope_create()
  val @(audited, counts) = _audit_names(names_text, names_len, 0, allowlist_text, allowlist_len, failing, 0, @(0, 0, 0, 0, 0, 0, 0))
  val @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors) = counts
  val () = println! ("== ", audited, " repositories, ", files, " workflow files: ", hashed, " passed by an allowlisted hash, ",
                     templated, " passed by a template, ", not_canonical, " not canonical, ", over_bound, " over the bound, ",
                     unreadable, " unreadable; ", repository_errors, " repository errors")
  val () = println! ("== allowlist: ", entries, " entries, ", bad_entries, " failing; templates: ", templates, " read, ", bad_templates, " failing")
  val chunks = $B.sized_rope_chunks(failing)
  val failed = _failures(counts) > 0 || bad_entries > 0 || bad_templates > 0 || audited = 0 || templates = 0: bool
  val () =
    if _failures(counts) > 0 then let
      val () = print! ("== failing repositories:")
      val () = _print_chunks(chunks)
    in println! () end
    else $B.rope_sized_list_free(chunks)
  val () = if audited = 0 then println! ("::error title=pin audit::the list held no repository") else ()
  val () = if templates = 0 then println! ("::error title=pin audit::no template was read") else ()
in if failed then 1 else 0 end

(* The status of the audit: 0 when every workflow file of every repository
   passes and the allowlist and the templates are whole, else 1 *)
#pub fn pin_audit_run (): int

implement pin_audit_run () = let
  var allow : $B.builder(0) = $B.create()
  val @(allow_end, allow_why) = read_constant("tools/pin-audit/allowlist.txt", allow)
  val @(allow_arr, allow_len) = $B.to_arr(allow)
  val @(allow_fz, allow_bv) = $A.freeze<byte>(allow_arr)
  val @(entries, bad_entries) =
    (case+ allow_end of
     | Read_whole() => allowlist_validate(allow_bv, allow_len)
     | Read_too_long() => let
         val () = println! ("::error title=pin audit::the allowlist tools/pin-audit/allowlist.txt is longer than the 524288 bytes the audit reads")
       in @(0, 1) end
     | Read_failed() => let
         val () = println! ("::error title=pin audit::the allowlist tools/pin-audit/allowlist.txt could not be read: ", allow_why)
       in @(0, 1) end): @(int, int)
  val allow_usable = (case+ allow_end of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
  val @(templates, bad_templates) = _templates_check()
  var names : $B.builder(0) = $B.create()
  val @(status, listed) = capture_with("gh", _list_argv(), no_arguments(), names)
  val @(names_arr, names_len) = $B.to_arr(names)
  val @(names_fz, names_bv) = $A.freeze<byte>(names_arr)
  val names_listed =
    (case+ listed of
     | Read_whole() =>
         if status = 0 then true
         else let
           val () = println! ("::error title=pin audit::the organisation's repositories could not be listed (gh status ", status, ")")
         in false end
     | Read_too_long() => let
         val () = println! ("::error title=pin audit::the list of the organisation's repositories is longer than the 524288 bytes the audit reads, so it would see part of it")
       in false end
     | Read_failed() => let
         val () = println! ("::error title=pin audit::the list of the organisation's repositories could not be read")
       in false end): bool
  val result =
    (if names_listed && allow_usable then _audit_all(names_bv, names_len, allow_bv, allow_len, entries, bad_entries, templates, bad_templates)
     else 1): int
  val () = $A.drop<byte>(names_fz, names_bv)
  val () = $A.free<byte>($A.thaw<byte>(names_fz))
  val () = $A.drop<byte>(allow_fz, allow_bv)
  val () = $A.free<byte>($A.thaw<byte>(allow_fz))
in result end
