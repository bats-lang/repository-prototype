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

(* The template whose file name is nbv[0, nk) (at most 255 bytes) against
   the file fb[0, fk); with report it says what it found *)
fn _try_template {ln,lf:agz}{nk:nat | nk <= 255}{fk:nat | fk <= 524288}
  (nbv: !$A.borrow(byte, ln, 1024), nk: int nk,
   fb: !$A.borrow(byte, lf, 524288), fk: int fk, report: bool): template_result = let
  var pb : $B.builder(0) = $B.create()
  val () = $B.bput(pb, "tools/pin-audit/templates/")
  val () = put_range(nbv, 0, nk, pb)
  val @(parr, pk) = $B.to_arr(pb)
  val @(pfz, pbv) = $A.freeze<byte>(parr)
  var content : $B.builder(0) = $B.create()
  val @(ended, why) = read_file(pbv, pk, content)
  val () = $A.drop<byte>(pfz, pbv)
  val () = $A.free<byte>($A.thaw<byte>(pfz))
  val @(carr, ck) = $B.to_arr(content)
  val @(cfz, cbv) = $A.freeze<byte>(carr)
  val result =
    (case+ ended of
     | Read_whole() => let
         val () =
           if report then let
             val () = print! ("   template ")
             val () = print_range(nbv, 0, nk)
           in println! (": read, ", ck, " bytes") end
           else ()
       in
         if template_matches(cbv, ck, fb, fk) then Template_equal() else Template_other()
       end
     | Read_too_long() => let
         val () = print! ("::error title=pin audit::template ")
         val () = print_range(nbv, 0, nk)
       in (println! (" is longer than the 524288 bytes the audit reads"); Template_unreadable()) end
     | Read_failed() => let
         val () = print! ("::error title=pin audit::template ")
         val () = print_range(nbv, 0, nk)
       in (println! (" could not be read: ", why); Template_unreadable()) end): template_result
  val () = $A.drop<byte>(cfz, cbv)
  val () = $A.free<byte>($A.thaw<byte>(cfz))
in result end

(* Entry i and after of the templates directory: the length of the name of
   the first template the file fb[0, fk) is (copied to name_out), else 0,
   with how many templates were read and how many could not be. With
   report, no template is looked for: every one is read and said. *)
fun _scan {n:nat}{i:nat | i <= n}{lf,lo:agz}{fk:nat | fk <= 524288} .<n - i>.
  (es: !$F.entries(n), n: int n, i: int i,
   fb: !$A.borrow(byte, lf, 524288), fk: int fk,
   name_out: !$A.arr(byte, lo, 256), report: bool, loaded: int, bad: int)
  : @([f:nat | f <= 255] int f, int, int) =
  if i >= n then @(0, loaded, bad)
  else let
    val nbuf = $A.alloc<byte>(1024)
    val nk = $F.entries_name(es, i, nbuf, 1024)
    val @(nfz, nbv) = $A.freeze<byte>(nbuf)
    val yml = (if nk >= 5 then lit_step(nbv, nk, nk - 4, ".yml") >= 0 else false): bool
    val @(found, loaded2, bad2) =
      (if ~yml then @(0, loaded, bad)
       else if nk > 255 then let
         val () = print! ("::error title=pin audit::a template name of ", nk, " bytes is longer than the 255 the audit will put in a path")
         val () = println! ()
       in @(0, loaded, bad + 1) end
       else
         (case+ _try_template(nbv, nk, fb, fk, report) of
          | Template_unreadable() => @(0, loaded, bad + 1)
          | Template_other() => @(0, loaded + 1, bad)
          | Template_equal() =>
              if report then @(0, loaded + 1, bad)
              else let val () = copy_into(nbv, nk, name_out) in @(nk, loaded + 1, bad) end)): @([f:nat | f <= 255] int f, int, int)
    val () = $A.drop<byte>(nfz, nbv)
    val () = $A.free<byte>($A.thaw<byte>(nfz))
  in
    if found > 0 then @(found, loaded2, bad2)
    else _scan(es, n, i + 1, fb, fk, name_out, report, loaded2, bad2)
  end

(* The name of the template the file fb[0, fk) is, in name_out[0, result),
   or 0 when it is none *)
fn _template_of {lf,lo:agz}{fk:nat | fk <= 524288}
  (fb: !$A.borrow(byte, lf, 524288), fk: int fk, name_out: !$A.arr(byte, lo, 256))
  : [f:nat | f <= 255] int f = let
  var pb : $B.builder(0) = $B.create()
  val () = $B.bput(pb, "tools/pin-audit/templates")
  val @(parr, pk) = $B.to_arr(pb)
  val @(pfz, pbv) = $A.freeze<byte>(parr)
  val listed = dir_entries(pbv, pk)
  val () = $A.drop<byte>(pfz, pbv)
  val () = $A.free<byte>($A.thaw<byte>(pfz))
in
  case+ listed of
  | ~$R.err(_) => 0
  | ~$R.ok(es) => let
      val @(found, _, _) = _scan(es, $F.entries_count(es), 0, fb, fk, name_out, false, 0, 0)
      val () = $F.entries_free(es)
    in found end
end

(* Reads every template once and says each: how many were read and how many
   could not be (a missing directory counts as one) *)
fn _templates_check (): @(int, int) = let
  var pb : $B.builder(0) = $B.create()
  val () = $B.bput(pb, "tools/pin-audit/templates")
  val @(parr, pk) = $B.to_arr(pb)
  val @(pfz, pbv) = $A.freeze<byte>(parr)
  val listed = dir_entries(pbv, pk)
  val () = $A.drop<byte>(pfz, pbv)
  val () = $A.free<byte>($A.thaw<byte>(pfz))
  val empty = $A.alloc<byte>(524288)
  val @(efz, ebv) = $A.freeze<byte>(empty)
  val r =
    (case+ listed of
     | ~$R.err(e) => let
         val () = println! ("::error title=pin audit::the templates directory tools/pin-audit/templates could not be read: ", $F.io_error_text(e))
       in @(0, 1) end
     | ~$R.ok(es) => let
         val name_out = $A.alloc<byte>(256)
         val @(_, loaded, bad) = _scan(es, $F.entries_count(es), 0, ebv, 0, name_out, true, 0, 0)
         val () = $A.free<byte>(name_out)
         val () = $F.entries_free(es)
       in @(loaded, bad) end): @(int, int)
  val () = $A.drop<byte>(efz, ebv)
  val () = $A.free<byte>($A.thaw<byte>(efz))
in r end

(* ============================================================
   The counts
   ============================================================ *)

(* Workflow files, those passed by their hash, those passed by a template,
   those not canonical, those over the bound, those unreadable, and the
   failures of a repository itself (its name, its clone, its list of
   workflows) *)
typedef tally = @(int, int, int, int, int, int, int)

(* One more file, in the column which (1 hash, 2 template, 3 not canonical,
   4 over the bound, 5 unreadable); which 6 is one more repository error and
   no file *)
fn _bump (t: tally, which: int): tally = let
  val @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors) = t
in
  if which = 1 then @(files + 1, hashed + 1, templated, not_canonical, over_bound, unreadable, repository_errors)
  else if which = 2 then @(files + 1, hashed, templated + 1, not_canonical, over_bound, unreadable, repository_errors)
  else if which = 3 then @(files + 1, hashed, templated, not_canonical + 1, over_bound, unreadable, repository_errors)
  else if which = 4 then @(files + 1, hashed, templated, not_canonical, over_bound + 1, unreadable, repository_errors)
  else if which = 5 then @(files + 1, hashed, templated, not_canonical, over_bound, unreadable + 1, repository_errors)
  else @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors + 1)
end

fn _failures (t: tally): int = let
  val @(_, _, _, not_canonical, over_bound, unreadable, repository_errors) = t
in not_canonical + over_bound + unreadable + repository_errors end

(* ============================================================
   One workflow file
   ============================================================ *)

(* The start of a file's failure line: the annotation, the repository, the
   path *)
fn _file_error {ln,lp:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe): void = let
  val () = print! ("::error title=pin audit::")
  val () = print_range(nb, s, e)
  val () = print! (": ")
  val () = print_range(pb, fs, fe)
in print! (": ") end

(* The start of a file's passing line *)
fn _file_pass {lp:agz}{fs,fe:nat | fs <= fe; fe <= 524288}
  (pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe): void = let
  val () = print! ("   ")
  val () = print_range(pb, fs, fe)
in print! (": pass, ") end

(* The file whose bytes are cb[0, ck) and whose sha256 is hb[0, 64): its
   verdict is printed and its column returned *)
fn _verdict {ln,lp,lc,lh,la:agz}{s,e,fs,fe,ck,ak:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288; ck <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe,
   cb: !$A.borrow(byte, lc, 524288), ck: int ck,
   hb: !$A.borrow(byte, lh, 64),
   ab: !$A.borrow(byte, la, 524288), ak: int ak): int = let
  val @(listed_at, slot, line_no) = allowlist_find(ab, ak, nb, s, e, pb, fs, fe, hb)
  val name_out = $A.alloc<byte>(256)
  val named = _template_of(cb, ck, name_out)
  val @(nfz, nbv) = $A.freeze<byte>(name_out)
  val listed = listed_at >= 0: bool
  val column =
    (if listed && named = 0 then let
       val () = _file_pass(pb, fs, fe)
       val () = print! ("its sha256 is the ")
       val () = (if slot = 1 then print! ("current") else print! ("next"))
       val () = print! (" hash of tools/pin-audit/allowlist.txt line ", line_no)
     in (println! (); 1) end
     else if ~listed && named > 0 then let
       val () = _file_pass(pb, fs, fe)
       val () = print! ("equal to the template ")
       val () = print_range(nbv, 0, named)
     in (println! (" with its holes filled"); 2) end
     else if listed then let
       val () = _file_error(nb, s, e, pb, fs, fe)
       val () = print! ("not canonical: its sha256 is listed in tools/pin-audit/allowlist.txt line ", line_no, " and it equals the template ")
       val () = print_range(nbv, 0, named)
     in (println! ("; exactly one may hold: drop the allowlist entry"); 3) end
     else let
       val () = _file_error(nb, s, e, pb, fs, fe)
       val () = print! ("not canonical: its sha256 ")
       val () = print_range(hb, 0, 64)
     in (println! (" is not listed for it in tools/pin-audit/allowlist.txt and it equals no template with its holes filled"); 3) end): int
  val () = $A.drop<byte>(nfz, nbv)
  val () = $A.free<byte>($A.thaw<byte>(nfz))
in column end

(* The file pb[fs, fe) of the clone of nb[s, e), at most 255 bytes of path
   and of name: read (at most 524288 bytes), hashed and judged *)
fn _audit_file_in {ln,lp,la:agz}{s,e,fs,fe,ak:nat | s <= e; e - s <= 255; e <= 524288; fs <= fe; fe - fs <= 255; fe <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe,
   symlink: bool, ab: !$A.borrow(byte, la, 524288), ak: int ak, t: tally): tally =
  if symlink then let
    val () = _file_error(nb, s, e, pb, fs, fe)
    val () = println! ("not canonical: it is a symbolic link (git mode 120000), which no template or hash describes")
  in _bump(t, 3) end
  else let
    var path : $B.builder(0) = $B.create()
    val () = $B.bput(path, "audit-clones/")
    val () = put_range(nb, s, e, path)
    val () = $B.bput(path, "/")
    val () = put_range(pb, fs, fe, path)
    val @(parr, pk) = $B.to_arr(path)
    val @(pfz, pbv) = $A.freeze<byte>(parr)
    var content : $B.builder(0) = $B.create()
    val @(ended, why) = read_file(pbv, pk, content)
    val () = $A.drop<byte>(pfz, pbv)
    val () = $A.free<byte>($A.thaw<byte>(pfz))
    val @(carr, ck) = $B.to_arr(content)
  in
    case+ ended of
    | Read_whole() => let
        val hex = sha256_hex(carr, ck)
        val @(hfz, hbv) = $A.freeze<byte>(hex)
        val @(cfz, cbv) = $A.freeze<byte>(carr)
        val column = _verdict(nb, s, e, pb, fs, fe, cbv, ck, hbv, ab, ak)
        val () = $A.drop<byte>(cfz, cbv)
        val () = $A.free<byte>($A.thaw<byte>(cfz))
        val () = $A.drop<byte>(hfz, hbv)
        val () = $A.free<byte>($A.thaw<byte>(hfz))
      in _bump(t, column) end
    | Read_too_long() => let
        val () = $A.free<byte>(carr)
        val () = _file_error(nb, s, e, pb, fs, fe)
        val () = println! ("over the bound: the file is longer than the 524288 bytes the audit reads, so it is not compared")
      in _bump(t, 4) end
    | Read_failed() => let
        val () = $A.free<byte>(carr)
        val () = _file_error(nb, s, e, pb, fs, fe)
        val () = println! ("unreadable: ", why)
      in _bump(t, 5) end
  end

(* The workflow file pb[fs, fe) of the repository nb[s, e) *)
fn _audit_file {ln,lp,la:agz}{s,e,fs,fe,ak:nat | s <= e; e - s <= 255; e <= 524288; fs <= fe; fe <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, lp, 524288), fs: int fs, fe: int fe,
   symlink: bool, ab: !$A.borrow(byte, la, 524288), ak: int ak, t: tally): tally =
  if fe - fs > 255 then let
    val () = _file_error(nb, s, e, pb, fs, fe)
    val () = println! ("over the bound: its path is ", fe - fs, " bytes, longer than the 255 the audit will put in a path")
  in _bump(t, 4) end
  else _audit_file_in(nb, s, e, pb, fs, fe, symlink, ab, ak, t)

(* ============================================================
   One repository
   ============================================================ *)

(* Whether nb[s, e) is a name the clone's path can hold: letters, digits,
   '.', '_' and '-', and not "." or "..". It goes into arguments, never a
   shell, and into audit-clones/<name>. *)
fn _name_ok {ln:agz}{s,e:nat | s <= e; e <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e): bool =
  if e <= s then false
  else if class_end(nb, e, s, 1) < e then false
  else if line_is(nb, s, e, ".") then false
  else if line_is(nb, s, e, "..") then false
  else true

(* The annotation that names the repository, ready for its message *)
fn _repository_error {ln:agz}{s,e:nat | s <= e; e <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e): void = let
  val () = print! ("::error title=pin audit::")
  val () = print_range(nb, s, e)
in print! (": ") end

fn _clone_argv {ln:agz}{s,e:nat | s <= e; e - s <= 255; e <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("git"),
  $L.list_vt_cons(arg_text("clone"),
  $L.list_vt_cons(arg_text("--quiet"),
  $L.list_vt_cons(arg_text("--depth"),
  $L.list_vt_cons(arg_text("1"),
  $L.list_vt_cons(arg_text("--"),
  $L.list_vt_cons(arg_range("https://github.com/bats-lang/", nb, s, e, ".git"),
  $L.list_vt_cons(arg_range("audit-clones/", nb, s, e, ""),
    $L.list_vt_nil()))))))))

(* The records of the listing of .github/workflows in the clone *)
fn _tree_argv {ln:agz}{s,e:nat | s <= e; e - s <= 255; e <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("git"),
  $L.list_vt_cons(arg_text("-C"),
  $L.list_vt_cons(arg_range("audit-clones/", nb, s, e, ""),
  $L.list_vt_cons(arg_text("ls-tree"),
  $L.list_vt_cons(arg_text("-z"),
  $L.list_vt_cons(arg_text("HEAD"),
  $L.list_vt_cons(arg_text(".github/workflows/"),
    $L.list_vt_nil())))))))

fn _nothing (): $L.listv($P.arg_entry) = $L.list_vt_nil()

(* Every record of ob[0, ok) from i, `<mode> <type> <object>\t<path>` and a
   zero byte (git ls-tree -z): a blob whose path ends in .yml or .yaml is a
   workflow file. A record not of that form is an error of the repository. *)
fun _records {ln,lo,la:agz}{s,e,ok,ak:nat | s <= e; e - s <= 255; e <= 524288; ok <= 524288; ak <= 524288}{i:nat | i <= ok} .<ok - i>.
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   ob: !$A.borrow(byte, lo, 524288), ok: int ok, i: int i,
   ab: !$A.borrow(byte, la, 524288), ak: int ak, t: tally): tally = let
  val j = find_byte(ob, ok, i, 0)
  val tab = find_byte(ob, j, i, 9)
  val sp1 = find_byte(ob, tab, i, 32)
  val t2 =
    (if j <= i then t
     else if tab >= j then let
       val () = _repository_error(nb, s, e)
     in (println! ("a record of the workflow listing has no tab"); _bump(t, 6)) end
     else if sp1 + 1 > tab then let
       val () = _repository_error(nb, s, e)
     in (println! ("a record of the workflow listing has no type"); _bump(t, 6)) end
     else let
       val sp2 = find_byte(ob, tab, sp1 + 1, 32)
       val blob = line_is(ob, sp1 + 1, sp2, "blob")
       val ps = tab + 1
       val yml = (if j - 4 >= ps then lit_step(ob, j, j - 4, ".yml") >= 0 else false): bool
       val yaml = (if j - 5 >= ps then lit_step(ob, j, j - 5, ".yaml") >= 0 else false): bool
     in
       if blob && (yml || yaml) then _audit_file(nb, s, e, ob, ps, j, line_is(ob, i, sp1, "120000"), ab, ak, t)
       else t
     end): tally
in
  if j >= ok then t2 else _records(nb, s, e, ob, ok, j + 1, ab, ak, t2)
end

(* The clone of nb[s, e) and its files *)
fn _audit_clone {ln,la:agz}{s,e,ak:nat | s <= e; e - s <= 255; e <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   ab: !$A.borrow(byte, la, 524288), ak: int ak, t: tally): tally = let
  var listing : $B.builder(0) = $B.create()
  val @(status, ended) = capture_with("git", _tree_argv(nb, s, e), _nothing(), listing)
  val @(larr, lk) = $B.to_arr(listing)
  val @(lfz, lbv) = $A.freeze<byte>(larr)
  val t2 =
    (case+ ended of
     | Read_whole() =>
         if status = 0 then _records(nb, s, e, lbv, lk, 0, ab, ak, t)
         else let
           val () = _repository_error(nb, s, e)
         in (println! ("git ls-tree could not list .github/workflows (status ", status, ")"); _bump(t, 6)) end
     | Read_too_long() => let
         val () = _repository_error(nb, s, e)
       in (println! ("over the bound: the list of workflow files is longer than the 524288 bytes the audit reads"); _bump(t, 4)) end
     | Read_failed() => let
         val () = _repository_error(nb, s, e)
       in (println! ("the list of workflow files could not be read"); _bump(t, 6)) end): tally
  val () = $A.drop<byte>(lfz, lbv)
  val () = $A.free<byte>($A.thaw<byte>(lfz))
in t2 end

(* Audits nb[s, e): its files from the counts t *)
fn _audit_one {ln,la:agz}{s,e,ak:nat | s <= e; e - s <= 255; e <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), s: int s, e: int e,
   ab: !$A.borrow(byte, la, 524288), ak: int ak, t: tally): tally =
  if ~_name_ok(nb, s, e) then let
    val () = _repository_error(nb, s, e)
  in (println! ("the repository's name is not one the audit will put in a path"); _bump(t, 6)) end
  else let
    val cloned = run_with("git", _clone_argv(nb, s, e), _nothing())
  in
    if cloned != 0 then let
      val () = _repository_error(nb, s, e)
    in (println! ("cannot be cloned (git status ", cloned, ")"); _bump(t, 6)) end
    else let
      val @(files_before, _, _, _, _, _, _) = t
      val t2 = _audit_clone(nb, s, e, ab, ak, t)
      val @(files_after, _, _, _, _, _, _) = t2
      val () = if files_after = files_before then println! ("   no workflow files") else ()
    in t2 end
  end

(* The failing names, in order, to standard output *)
fun _print_chunks {n:nat} .<n>. (chunks: $B.rope_sized_list(n)): void =
  case+ chunks of
  | ~$B.rope_sized_nil() => ()
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(fz, bv) = $A.freeze<byte>(chunk)
      val () = print_range(bv, 0, used)
      val () = $A.drop<byte>(fz, bv)
      val () = $A.free<byte>($A.thaw<byte>(fz))
    in _print_chunks(rest) end

(* Every name in nb[0, nk) from i, one on each line: audited with the counts
   going on from t, the failing ones going into failing. A name over 255
   bytes is a failure of its own, said and counted. *)
fun _audit_names {ln,la:agz}{nk,ak:nat | nk <= 524288; ak <= 524288}{i:nat | i <= nk} .<nk - i>.
  (nb: !$A.borrow(byte, ln, 524288), nk: int nk, i: int i,
   ab: !$A.borrow(byte, la, 524288), ak: int ak,
   failing: !$B.sized_rope, audited: int, t: tally): @(int, tally) = let
  val j = line_end(nb, nk, i)
  val @(audited2, t2) =
    (if j <= i then @(audited, t)
     else let
       val () = (print! ("== "); print_range(nb, i, j); println! ())
       val before = _failures(t)
       val t3 =
         (if j - i <= 255 then _audit_one(nb, i, j, ab, ak, t)
          else let
            val () = _repository_error(nb, i, j)
          in (println! ("the repository's name is ", j - i, " bytes, longer than the 255 the audit will put in a path"); _bump(t, 6)) end): tally
       val () =
         if _failures(t3) > before then let
           val () = $B.sized_rope_put(failing, 32)
         in $B.sized_rope_copy(failing, nb, i, j) end
         else ()
     in @(audited + 1, t3) end): @(int, tally)
in
  if j >= nk then @(audited2, t2) else _audit_names(nb, nk, j + 1, ab, ak, failing, audited2, t2)
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

(* The audit of the names in nb[0, nk) with the allowlist ab[0, ak): the
   status of the run *)
fn _audit_all {ln,la:agz}{nk,ak:nat | nk <= 524288; ak <= 524288}
  (nb: !$A.borrow(byte, ln, 524288), nk: int nk,
   ab: !$A.borrow(byte, la, 524288), ak: int ak,
   entries: int, bad_entries: int, templates: int, bad_templates: int): int = let
  var failing : $B.sized_rope = $B.sized_rope_create()
  val @(audited, t) = _audit_names(nb, nk, 0, ab, ak, failing, 0, @(0, 0, 0, 0, 0, 0, 0))
  val @(files, hashed, templated, not_canonical, over_bound, unreadable, repository_errors) = t
  val () = println! ("== ", audited, " repositories, ", files, " workflow files: ", hashed, " passed by an allowlisted hash, ",
                     templated, " passed by a template, ", not_canonical, " not canonical, ", over_bound, " over the bound, ",
                     unreadable, " unreadable; ", repository_errors, " repository errors")
  val () = println! ("== allowlist: ", entries, " entries, ", bad_entries, " failing; templates: ", templates, " read, ", bad_templates, " failing")
  val chunks = $B.sized_rope_chunks(failing)
  val failed = _failures(t) > 0 || bad_entries > 0 || bad_templates > 0 || audited = 0 || templates = 0: bool
  val () =
    if _failures(t) > 0 then let
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
  val @(status, listed) = capture_with("gh", _list_argv(), _nothing(), names)
  val @(names_arr, names_len) = $B.to_arr(names)
  val @(names_fz, names_bv) = $A.freeze<byte>(names_arr)
  val ok =
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
    (if ok && allow_usable then _audit_all(names_bv, names_len, allow_bv, allow_len, entries, bad_entries, templates, bad_templates)
     else 1): int
  val () = $A.drop<byte>(names_fz, names_bv)
  val () = $A.free<byte>($A.thaw<byte>(names_fz))
  val () = $A.drop<byte>(allow_fz, allow_bv)
  val () = $A.free<byte>($A.thaw<byte>(allow_fz))
in result end
