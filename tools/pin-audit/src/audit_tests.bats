(* audit_tests -- the tests of pin-audit (bats-lang/repository-prototype#396),
   run by `bats test` in tools/pin-audit after `bats build`.

   Each case plants repositories with `git init` under
   build/pin-audit-tests/<case>/planted/<name>.git, a copy of the templates,
   an allowlist and a stand-in `gh` (the package's own gh_stand_in binary,
   copied as bin/gh), and runs the built dist/debug/pin_audit there with
   GIT_CONFIG_GLOBAL mapping https://github.com/bats-lang/ to the planted
   directory (url.<dir>.insteadOf) and PATH starting at the stand-in's
   directory. The audit's output and exit status are what is judged. A
   case's directory is kept when it fails (and when it passes: `bats clean`
   removes build/), and a failing case prints the audit's whole output.
   Keyword: pin-audit tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use list as L
#use process as P
#use result as R

staload "support.sats"
staload "template.sats"
staload "allowlist.sats"

(* ============================================================
   Commands
   ============================================================ *)

fn _len {sn:nat} (s: string sn): int sn = g1u2i(string1_length(s))

fn _nothing (): $L.listv($P.arg_entry) = $L.list_vt_nil()

fn _l1 (a: $P.arg_entry): $L.listv($P.arg_entry) =
  $L.list_vt_cons(a, $L.list_vt_nil())

fn _l2 (a: $P.arg_entry, b: $P.arg_entry): $L.listv($P.arg_entry) =
  $L.list_vt_cons(a, _l1(b))

fn _l3 (a: $P.arg_entry, b: $P.arg_entry, c: $P.arg_entry): $L.listv($P.arg_entry) =
  $L.list_vt_cons(a, _l2(b, c))

fn _l4 (a: $P.arg_entry, b: $P.arg_entry, c: $P.arg_entry, d: $P.arg_entry): $L.listv($P.arg_entry) =
  $L.list_vt_cons(a, _l3(b, c, d))

(* program with the arguments, whose first is the program's own name: its
   status, ~1 when it could not be run *)
fn _run {pn:nat | pn < 4096} (prog: string pn, args: $L.listv($P.arg_entry)): int =
  run_with(prog, $L.list_vt_cons(arg_text(prog), args), _nothing())

fn _join2 {an,bn:nat | an < 4096; bn < 4096} (a: string an, b: string bn): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, a)
  val () = $B.bput(out, b)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* dir/planted/name.git *)
fn _repo_arg {dn,nn:nat | dn < 200; nn < 100} (dir: string dn, name: string nn): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/planted/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, ".git")
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* ============================================================
   Files
   ============================================================ *)

vtypedef path_text = [l:agz][k:nat | k < 1000] @($A.arr(byte, l, 524288), int k)

(* dir/planted/name.git/rel *)
fn _repo_path {dn,nn,rn,fn_:nat | dn < 200; nn < 100; rn < 300; fn_ < 300}
  (dir: string dn, name: string nn, rel: string rn, file: string fn_): path_text = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/planted/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, ".git/")
  val () = $B.bput(out, rel)
  val () = $B.bput(out, file)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* dir/rel *)
fn _case_path {dn,rn:nat | dn < 200; rn < 300} (dir: string dn, rel: string rn): path_text = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/")
  val () = $B.bput(out, rel)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

fun _write_chunks {n:nat}{l:agz}{pn:pos}{m:nat | m <= pn; m < 524288} .<n>.
  (p: !$A.borrow(byte, l, pn), m: int m, chunks: $B.rope_sized_list(n), append: bool): bool =
  case+ chunks of
  | ~$B.rope_sized_nil() => true
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(fz, bv) = $A.freeze<byte>(chunk)
      val ok = write_file(p, m, bv, used, append)
      val () = $A.drop<byte>(fz, bv)
      val () = $A.free<byte>($A.thaw<byte>(fz))
      val ok_rest = _write_chunks(p, m, rest, true)
    in ok && ok_rest end

(* The rope written to the file at the path (made or emptied first) *)
fn _write_rope(path: path_text, text: $B.sized_rope): bool = let
  val @(parr, pk) = path
  val @(pfz, pbv) = $A.freeze<byte>(parr)
  val ok = _write_chunks(pbv, pk, $B.sized_rope_chunks(text), false)
  val () = $A.drop<byte>(pfz, pbv)
  val () = $A.free<byte>($A.thaw<byte>(pfz))
in ok end

fun _put_repeated {n:nat} .<n>. (r: !$B.sized_rope, n: int n): void =
  if n <= 0 then ()
  else let
    val () = $B.sized_rope_put(r, 97)
  in _put_repeated(r, n - 1) end

(* ============================================================
   A case's directory
   ============================================================ *)

(* A fresh dir: the templates, the stand-in gh, an allowlist with no entry
   and an empty name list. The old one, if any, is removed first. *)
fn _fresh {dn:nat | dn < 200} (dir: string dn): void = let
  val _ = _run("rm", _l3(arg_text("-rf"), arg_text("--"), arg_text(dir)))
  val _ = _run("mkdir", $L.list_vt_cons(arg_text("-p"), $L.list_vt_cons(arg_text("--"),
            _l3(_join2(dir, "/tools/pin-audit"), _join2(dir, "/planted"), _join2(dir, "/bin")))))
  val _ = _run("cp", _l3(arg_text("-R"), arg_text("templates"), _join2(dir, "/tools/pin-audit/templates")))
  val _ = _run("cp", _l2(arg_text("dist/debug/gh_stand_in"), _join2(dir, "/bin/gh")))
  var allowlist : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(allowlist, "# no entries\n")
  val _ = _write_rope(_case_path(dir, "tools/pin-audit/allowlist.txt"), allowlist)
  var names : $B.sized_rope = $B.sized_rope_create()
  val _ = _write_rope(_case_path(dir, "gh-names.txt"), names)
in () end

(* The repository dir/planted/name.git, a new one, with no commit *)
fn _plant {dn,nn:nat | dn < 200; nn < 100} (dir: string dn, name: string nn): void = let
  val _ = _run("git", _l3(arg_text("init"), arg_text("-q"), _repo_arg(dir, name)))
in () end

(* The repository's commit of everything written in it *)
fn _commit {dn,nn:nat | dn < 200; nn < 100} (dir: string dn, name: string nn): void = let
  val _ = _run("git", _l4(arg_text("-C"), _repo_arg(dir, name), arg_text("add"), arg_text("-A")))
  val _ = _run("git", $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_repo_arg(dir, name),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.name=plant"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.email=plant@example.com"),
            _l4(arg_text("commit"), arg_text("-q"), arg_text("-m"), arg_text("plant")))))))))
in () end

(* The rope as a file of the planted repository, in folder rel (a
   directory is made) *)
fn _put_rope {dn,nn,rn,fn_:nat | dn < 200; nn < 100; rn < 300; fn_ < 300}
  (dir: string dn, name: string nn, rel: string rn, file: string fn_, text: $B.sized_rope): void = let
  val _ = _run("mkdir", _l3(arg_text("-p"), arg_text("--"), _join2(dir, "/planted/")))
  var folder : $B.builder(0) = $B.create()
  val () = $B.bput(folder, dir)
  val () = $B.bput(folder, "/planted/")
  val () = $B.bput(folder, name)
  val () = $B.bput(folder, ".git/")
  val () = $B.bput(folder, rel)
  val @(farr, fk) = $B.to_arr(folder)
  val _ = _run("mkdir", _l3(arg_text("-p"), arg_text("--"), @(farr, fk)))
  val _ = _write_rope(_repo_path(dir, name, rel, file), text)
in () end

(* The text of a file of the planted repository *)
fn _put {dn,nn,rn,fn_,cn:nat | dn < 200; nn < 100; rn < 300; fn_ < 300; cn < 100000}
  (dir: string dn, name: string nn, rel: string rn, file: string fn_, content: string cn): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
in _put_rope(dir, name, rel, file, text) end

(* A workflow file of the planted repository *)
fn _workflow {dn,nn,fn_,cn:nat | dn < 200; nn < 100; fn_ < 300; cn < 100000}
  (dir: string dn, name: string nn, file: string fn_, content: string cn): void =
  _put(dir, name, ".github/workflows/", file, content)

fun _fill_loop {l:agz}{tk:nat | tk <= 524288}{t:nat | t <= tk}{cn,mn,nn:nat} .<tk - t>.
  (tb: !$A.borrow(byte, l, 524288), tk: int tk, t: int t, out: !$B.sized_rope,
   commit: string cn, comment: string mn, minute: string nn, mutate: int): void = let
  val c = lit_step(tb, tk, t, "@@COMMIT@@")
in
  if c >= 0 then let
    val () = $B.sized_rope_bput(out, commit)
  in _fill_loop(tb, tk, c, out, commit, comment, minute, mutate) end
  else let
    val m = lit_step(tb, tk, t, "@@COMMENT@@")
  in
    if m >= 0 then let
      val () = $B.sized_rope_bput(out, comment)
    in _fill_loop(tb, tk, m, out, commit, comment, minute, mutate) end
    else let
      val n = lit_step(tb, tk, t, "@@MINUTE@@")
    in
      if n >= 0 then let
        val () = $B.sized_rope_bput(out, minute)
      in _fill_loop(tb, tk, n, out, commit, comment, minute, mutate) end
      else if t >= tk then ()
      else let
        val b = byte2int0($A.read<byte>(tb, t))
        val () = $B.sized_rope_put(out, $AR.low_byte(if t = mutate then 126 else b))
      in _fill_loop(tb, tk, t + 1, out, commit, comment, minute, mutate) end
    end
  end
end

(* The template at template_path with its holes filled with the values
   (mutate: the place of one byte of a segment changed to `~`, or ~1), as
   a workflow file of the planted repository *)
fn _fill {dn,nn,fn_,tn,cn,mn,hn:nat | dn < 200; nn < 100; fn_ < 300; tn < 4096}
  (dir: string dn, name: string nn, file: string fn_, template_path: string tn,
   commit: string cn, comment: string mn, minute: string hn, mutate: int): void = let
  var template : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant(template_path, template)
  val @(tarr, tk) = $B.to_arr(template)
  val @(tfz, tbv) = $A.freeze<byte>(tarr)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = _fill_loop(tbv, tk, 0, text, commit, comment, minute, mutate)
  val () = $A.drop<byte>(tfz, tbv)
  val () = $A.free<byte>($A.thaw<byte>(tfz))
in _put_rope(dir, name, ".github/workflows/", file, text) end

(* The sha256 of the text, as 64 digits, appended to the rope *)
fn _hash_into {cn:nat | cn < 100000} (text: !$B.sized_rope, content: string cn): void = let
  var body : $B.builder(0) = $B.create()
  val () = $B.bput(body, content)
  val @(arr, k) = $B.to_arr(body)
  val hex = sha256_hex(arr, k)
  val () = $A.free<byte>(arr)
  val @(hfz, hbv) = $A.freeze<byte>(hex)
  val () = $B.sized_rope_copy(text, hbv, 0, 64)
  val () = $A.drop<byte>(hfz, hbv)
  val () = $A.free<byte>($A.thaw<byte>(hfz))
in () end

(* The allowlist of the case: one entry, the key, the sha256 of the first
   content, the sha256 of the second when it is not empty, and ` # ` and
   the comment when it is not empty *)
fn _allow {dn,kn,an,bn,cn:nat | dn < 200; kn < 1000; an < 100000; bn < 100000; cn < 1000}
  (dir: string dn, key: string kn, first: string an, second: string bn, comment: string cn): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, key)
  val () = $B.sized_rope_bput(text, " ")
  val () = _hash_into(text, first)
  val () =
    if _len(second) > 0 then let
      val () = $B.sized_rope_bput(text, " ")
    in _hash_into(text, second) end
    else ()
  val () =
    if _len(comment) > 0 then let
      val () = $B.sized_rope_bput(text, " # ")
    in $B.sized_rope_bput(text, comment) end
    else ()
  val () = $B.sized_rope_bput(text, "\n")
  val _ = _write_rope(_case_path(dir, "tools/pin-audit/allowlist.txt"), text)
in () end

(* The allowlist of the case, as written *)
fn _allow_raw {dn,cn:nat | dn < 200; cn < 100000} (dir: string dn, content: string cn): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = _write_rope(_case_path(dir, "tools/pin-audit/allowlist.txt"), text)
in () end

(* The names gh prints, one on each line *)
fn _names {dn,cn:nat | dn < 200; cn < 100000} (dir: string dn, content: string cn): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = _write_rope(_case_path(dir, "gh-names.txt"), text)
in () end

(* A file of the case (an empty one: gh-fail makes the stand-in exit 1,
   gh-flood makes it print more than the audit reads) *)
fn _flag {dn,fn_:nat | dn < 200; fn_ < 300} (dir: string dn, file: string fn_): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val _ = _write_rope(_case_path(dir, file), text)
in () end

(* The current directory, in an array of 4096 bytes: its length *)
fn _cwd {l:agz} (buf: !$A.arr(byte, l, 4096)): [k:nat | k <= 4096] int k =
  case+ $E.cwd_read(buf, 4096) of
  | ~$R.some(k) => k
  | ~$R.none() => 0

(* gitconfig of the case: https://github.com/bats-lang/ is the directory of
   its planted repositories (url.<dir>.insteadOf) *)
fn _config {dn:nat | dn < 200} (dir: string dn): void = let
  val cwd = $A.alloc<byte>(4096)
  val ck = _cwd(cwd)
  val @(cfz, cbv) = $A.freeze<byte>(cwd)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, "[url \"file://")
  val () = $B.sized_rope_copy(text, cbv, 0, ck)
  val () = $B.sized_rope_bput(text, "/")
  val () = $B.sized_rope_bput(text, dir)
  val () = $B.sized_rope_bput(text, "/planted/\"]\n\tinsteadOf = https://github.com/bats-lang/\n")
  val _ = _write_rope(_case_path(dir, "gitconfig"), text)
  val () = $A.drop<byte>(cfz, cbv)
  val () = $A.free<byte>($A.thaw<byte>(cfz))
in () end

(* ============================================================
   Running the audit
   ============================================================ *)

(* The built audit in dir, with the stand-in gh first on PATH and the
   planted repositories behind GIT_CONFIG_GLOBAL: its exit status, its
   output in out *)
fn _audit {dn:nat | dn < 200} (dir: string dn, out: !$B.builder(0) >> $B.builder_v): @(int, read_end) = let
  val () = _config(dir)
  val cwd = $A.alloc<byte>(4096)
  val ck = _cwd(cwd)
  val @(cfz, cbv) = $A.freeze<byte>(cwd)
  var pname : $B.builder(0) = $B.create()
  val () = $B.bput(pname, "PATH")
  val @(parr, _) = $B.to_arr(pname)
  val old = $A.alloc<byte>(8192)
  val ok = (case+ $E.get_cstr(parr, 524288, old, 8192) of | ~$R.some(k) => k | ~$R.none() => 0): [k:nat | k <= 8192] int k
  val () = $A.free<byte>(parr)
  val @(ofz, obv) = $A.freeze<byte>(old)
  var path_entry : $B.builder(0) = $B.create()
  val () = $B.bput(path_entry, "PATH=")
  val () = put_range(cbv, 0, ck, path_entry)
  val () = $B.bput(path_entry, "/")
  val () = $B.bput(path_entry, dir)
  val () = $B.bput(path_entry, "/bin:")
  val () = put_range(obv, 0, ok, path_entry)
  val @(pe_arr, pe_k) = $B.to_arr(path_entry)
  var config_entry : $B.builder(0) = $B.create()
  val () = $B.bput(config_entry, "GIT_CONFIG_GLOBAL=")
  val () = put_range(cbv, 0, ck, config_entry)
  val () = $B.bput(config_entry, "/")
  val () = $B.bput(config_entry, dir)
  val () = $B.bput(config_entry, "/gitconfig")
  val @(ce_arr, ce_k) = $B.to_arr(config_entry)
  val result = capture_with("env",
    _l4(arg_text("env"), arg_text("-C"), arg_text(dir), arg_text("../../../dist/debug/pin_audit")),
    _l2(@(pe_arr, pe_k), @(ce_arr, ce_k)), out)
  val () = $A.drop<byte>(ofz, obv)
  val () = $A.free<byte>($A.thaw<byte>(ofz))
  val () = $A.drop<byte>(cfz, cbv)
  val () = $A.free<byte>($A.thaw<byte>(cfz))
in result end

fun _contains {l:agz}{ok:nat | ok <= 524288}{i:nat | i <= ok}{sn:pos} .<ok - i>.
  (ob: !$A.borrow(byte, l, 524288), ok: int ok, i: int i, needle: string sn): bool =
  if i >= ok then false
  else if lit_step(ob, ok, i, needle) >= 0 then true
  else _contains(ob, ok, i + 1, needle)

(* Whether the output holds the text; the empty text is always held *)
fn _has {l:agz}{ok:nat | ok <= 524288} {sn:nat}
  (ob: !$A.borrow(byte, l, 524288), ok: int ok, needle: string sn): bool =
  if _len(needle) > 0 then _contains(ob, ok, 0, needle) else true

(* Whether the output lacks the text; the empty text is always lacked *)
fn _lacks {l:agz}{ok:nat | ok <= 524288} {sn:nat}
  (ob: !$A.borrow(byte, l, 524288), ok: int ok, needle: string sn): bool =
  if _len(needle) > 0 then ~_contains(ob, ok, 0, needle) else true

(* Runs the case and judges it: the exit status is want, the output holds
   the three texts and lacks the last. A failing case prints what it saw. *)
fn _judge {dn,an,bn,cn,xn:nat | dn < 200}
  (dir: string dn, want: int, first: string an, second: string bn, third: string cn, absent: string xn): bool = let
  var out : $B.builder(0) = $B.create()
  val @(status, ended) = _audit(dir, out)
  val @(oarr, ok) = $B.to_arr(out)
  val @(ofz, obv) = $A.freeze<byte>(oarr)
  val whole = (case+ ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
  val good = whole && status = want && _has(obv, ok, first) && _has(obv, ok, second) && _has(obv, ok, third) && _lacks(obv, ok, absent): bool
  val () =
    if good then ()
    else let
      val () = println! ("FAIL ", dir, ": exit status ", status, " (wanted ", want, "), the output was read whole: ", whole)
      val () = println! ("  wanted: ", first, " | ", second, " | ", third, " | and lacking: ", absent)
      val () = println! ("  the audit's output:")
      val () = print_range(obv, 0, ok)
    in println! ("  (the case's directory ", dir, " is kept)") end
  val () = $A.drop<byte>(ofz, obv)
  val () = $A.free<byte>($A.thaw<byte>(ofz))
in good end

(* ============================================================
   The templates' holes, in the matcher
   ============================================================ *)

(* Whether the file is the template, each as a text of its own *)
fn _matches {tn,fn_:nat | tn < 4096; fn_ < 4096} (template: string tn, file: string fn_): bool = let
  var tb : $B.builder(0) = $B.create()
  val () = $B.bput(tb, template)
  val @(tarr, tk) = $B.to_arr(tb)
  var fb : $B.builder(0) = $B.create()
  val () = $B.bput(fb, file)
  val @(farr, fk) = $B.to_arr(fb)
  val @(tfz, tbv) = $A.freeze<byte>(tarr)
  val @(ffz, fbv) = $A.freeze<byte>(farr)
  val result = template_matches(tbv, tk, fbv, fk)
  val () = $A.drop<byte>(ffz, fbv)
  val () = $A.free<byte>($A.thaw<byte>(ffz))
  val () = $A.drop<byte>(tfz, tbv)
  val () = $A.free<byte>($A.thaw<byte>(tfz))
in result end

$UNITTEST.run begin

(* The commit hole: exactly 40 lowercase hexadecimal digits *)
fn test_hole_commit_class (): bool =
  _matches("a@@COMMIT@@b", "a0123456789abcdef0123456789abcdef01234567b")
  && ~_matches("a@@COMMIT@@b", "a0123456789abcdef0123456789abcdef0123456b")
  && ~_matches("a@@COMMIT@@b", "a0123456789abcdef0123456789abcdef012345678b")
  && ~_matches("a@@COMMIT@@b", "a0123456789ABCDEF0123456789abcdef01234567b")
  && ~_matches("a@@COMMIT@@b", "a0123456789abcdef0123456789abcdef0123456gb")
  && ~_matches("a@@COMMIT@@b", "ab")

(* The comment hole: one or more printable ASCII characters, to the end of
   the line *)
fn test_hole_comment_class (): bool =
  _matches("x # @@COMMENT@@\n", "x # repository-prototype main 0123abc\n")
  && _matches("x # @@COMMENT@@\n", "x # a\n")
  && _matches("x # @@COMMENT@@\n", "x # ~ #!\"\n")
  && ~_matches("x # @@COMMENT@@\n", "x # \n")
  && ~_matches("x # @@COMMENT@@\n", "x # a\tb\n")
  && ~_matches("x # @@COMMENT@@\n", "x # a\r\n")
  && ~_matches("x # @@COMMENT@@\n", "x # a")
  && ~_matches("x # @@COMMENT@@\n", "x # a\nb\n")

(* The minute hole: one or two digits *)
fn test_hole_minute_class (): bool =
  _matches("'@@MINUTE@@ 5 * * *'", "'7 5 * * *'")
  && _matches("'@@MINUTE@@ 5 * * *'", "'17 5 * * *'")
  && _matches("'@@MINUTE@@ 5 * * *'", "'59 5 * * *'")
  && ~_matches("'@@MINUTE@@ 5 * * *'", "'123 5 * * *'")
  && ~_matches("'@@MINUTE@@ 5 * * *'", "' 5 * * *'")
  && ~_matches("'@@MINUTE@@ 5 * * *'", "'a 5 * * *'")
  && ~_matches("'@@MINUTE@@ 5 * * *'", "'-1 5 * * *'")

(* A segment is compared byte for byte, and the file ends where the
   template does *)
fn test_segments_are_exact (): bool =
  _matches("abc @@MINUTE@@ def\n", "abc 1 def\n")
  && ~_matches("abc @@MINUTE@@ def\n", "abd 1 def\n")
  && ~_matches("abc @@MINUTE@@ def\n", "abc 1 def")
  && ~_matches("abc @@MINUTE@@ def\n", "abc 1 def\n\n")
  && ~_matches("abc @@MINUTE@@ def\n", "abc 1 de\n")
  && ~_matches("abc @@MINUTE@@ def\n", "abc 1  def\n")
  && _matches("", "")
  && ~_matches("", "a")

end

(* ============================================================
   Planted repositories
   ============================================================ *)

$UNITTEST.run begin

(* Canonical callers pass: each template with its holes filled, the minute
   of one digit and of two *)
fn test_canonical_callers_pass (): bool = let
  val dir = "build/pin-audit-tests/canonical"
  val () = _fresh(dir)
  val () = _plant(dir, "ok")
  val () = _fill(dir, "ok", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _fill(dir, "ok", "relock.yml", "templates/relock.yml", "89abcdef0123456789abcdef0123456789abcdef", "repository-prototype main 89abcde", "7", ~1)
  val () = _fill(dir, "ok", "publish.yml", "templates/publish.yml", "0123456789abcdef0123456789abcdef01234567", "x", "0", ~1)
  val () = _commit(dir, "ok")
  val () = _names(dir, "ok\n")
in _judge(dir, 0, ".github/workflows/check.yml: pass, equal to the template check.yml", ".github/workflows/relock.yml: pass, equal to the template relock.yml",
          ".github/workflows/publish.yml: pass, equal to the template publish.yml", "::error") end

(* A canonical file with one byte changed fails *)
fn test_one_byte_changed_fails (): bool = let
  val dir = "build/pin-audit-tests/one-byte"
  val () = _fresh(dir)
  val () = _plant(dir, "changed")
  val () = _fill(dir, "changed", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", 5)
  val () = _commit(dir, "changed")
  val () = _names(dir, "changed\n")
in _judge(dir, 1, "::error title=pin audit::changed: .github/workflows/check.yml: not canonical", "1 not canonical", "", "pass, equal") end

(* The commit hole outside its class (uppercase digits) fails *)
fn test_commit_hole_outside_class_fails (): bool = let
  val dir = "build/pin-audit-tests/commit-hole"
  val () = _fresh(dir)
  val () = _plant(dir, "bad")
  val () = _fill(dir, "bad", "check.yml", "templates/check.yml", "0123456789ABCDEF0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _commit(dir, "bad")
  val () = _names(dir, "bad\n")
in _judge(dir, 1, "bad: .github/workflows/check.yml: not canonical", "1 not canonical", "", "pass, equal") end

(* The comment hole outside its class (a tab) fails *)
fn test_comment_hole_outside_class_fails (): bool = let
  val dir = "build/pin-audit-tests/comment-hole"
  val () = _fresh(dir)
  val () = _plant(dir, "bad")
  val () = _fill(dir, "bad", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "a\tb", "17", ~1)
  val () = _commit(dir, "bad")
  val () = _names(dir, "bad\n")
in _judge(dir, 1, "bad: .github/workflows/check.yml: not canonical", "1 not canonical", "", "pass, equal") end

(* The minute hole outside its class (three digits) fails *)
fn test_minute_hole_outside_class_fails (): bool = let
  val dir = "build/pin-audit-tests/minute-hole"
  val () = _fresh(dir)
  val () = _plant(dir, "bad")
  val () = _fill(dir, "bad", "relock.yml", "templates/relock.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "123", ~1)
  val () = _commit(dir, "bad")
  val () = _names(dir, "bad\n")
in _judge(dir, 1, "bad: .github/workflows/relock.yml: not canonical", "1 not canonical", "", "pass, equal") end

(* A file listed with two hashes passes with the current one *)
fn test_listed_current_hash_passes (): bool = let
  val dir = "build/pin-audit-tests/hash-current"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "name: next\non: push\n", "bespoke#1")
in _judge(dir, 0, "own.yml: pass, its sha256 is the current hash of tools/pin-audit/allowlist.txt line 1", "1 passed by an allowlisted hash", "", "::error") end

(* ... and with the next one *)
fn test_listed_next_hash_passes (): bool = let
  val dir = "build/pin-audit-tests/hash-next"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: next\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "name: next\non: push\n", "bespoke#1")
in _judge(dir, 0, "own.yml: pass, its sha256 is the next hash of tools/pin-audit/allowlist.txt line 1", "1 passed by an allowlisted hash", "", "::error") end

(* ... and fails with a third *)
fn test_listed_third_hash_fails (): bool = let
  val dir = "build/pin-audit-tests/hash-third"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: third\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "name: next\non: push\n", "bespoke#1")
in _judge(dir, 1, "bespoke: .github/workflows/own.yml: not canonical: its sha256 ", "is not listed for it in tools/pin-audit/allowlist.txt", "1 not canonical", "pass, its") end

(* An entry whose comment is `canonical` passes *)
fn test_canonical_comment_passes (): bool = let
  val dir = "build/pin-audit-tests/canonical-comment"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "", "canonical")
in _judge(dir, 0, "own.yml: pass, its sha256 is the current hash", "0 failing", "", "::error") end

(* An entry with no ticket comment fails the audit, named, and lists
   nothing *)
fn test_entry_without_ticket_comment_fails (): bool = let
  val dir = "build/pin-audit-tests/no-comment"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "", "")
in _judge(dir, 1, "::error title=pin audit::allowlist.txt line 1: it has no ticket comment", "bespoke: .github/workflows/own.yml: not canonical", "1 entries, 1 failing", "pass, its") end

(* A comment that names no ticket fails the same way *)
fn test_entry_with_other_comment_fails (): bool = let
  val dir = "build/pin-audit-tests/other-comment"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "", "fix it later")
in _judge(dir, 1, "allowlist.txt line 1: it has no ticket comment", "bespoke: .github/workflows/own.yml: not canonical", "", "pass, its") end

(* Three hashes are not an entry, and a file listed twice is not either *)
fn test_malformed_entries_fail (): bool = let
  val dir = "build/pin-audit-tests/malformed"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow_raw(dir, "bespoke/a.yml 0000000000000000000000000000000000000000000000000000000000000000 1111111111111111111111111111111111111111111111111111111111111111 2222222222222222222222222222222222222222222222222222222222222222 # bespoke#1\nbespoke/b.yml 0000000000000000000000000000000000000000000000000000000000000000 # bespoke#1\nbespoke/b.yml 1111111111111111111111111111111111111111111111111111111111111111 # bespoke#1\nbespoke/c.yml 00 # bespoke#1\nnot an entry\n")
in _judge(dir, 1, "allowlist.txt line 1: it is not one or two hashes", "allowlist.txt line 3: it is listed twice", "allowlist.txt line 4: it has no 64-digit lowercase sha256", "") end

(* A repository with no workflow file passes, said *)
fn test_repository_without_workflows_passes (): bool = let
  val dir = "build/pin-audit-tests/no-workflows"
  val () = _fresh(dir)
  val () = _plant(dir, "quiet")
  val () = _put(dir, "quiet", "", "README.md", "nothing here\n")
  val () = _commit(dir, "quiet")
  val () = _names(dir, "quiet\n")
in _judge(dir, 0, "== quiet\n   no workflow files", "1 repositories, 0 workflow files", "", "::error") end

(* A path over the bound is a failure of its own, said and counted *)
fn test_path_over_bound_fails (): bool = let
  val dir = "build/pin-audit-tests/long-path"
  val () = _fresh(dir)
  val () = _plant(dir, "long")
  val () = _workflow(dir, "long", "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa.yml", "name: x\n")
  val () = _commit(dir, "long")
  val () = _names(dir, "long\n")
in _judge(dir, 1, "over the bound: its path is 258 bytes, longer than the 255", "1 over the bound", "", "pass, ") end

(* A file over the bound is a failure of its own, said and counted *)
fn test_file_over_bound_fails (): bool = let
  val dir = "build/pin-audit-tests/big-file"
  val () = _fresh(dir)
  val () = _plant(dir, "big")
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = _put_repeated(text, 600000)
  val () = _put_rope(dir, "big", ".github/workflows/", "big.yml", text)
  val () = _commit(dir, "big")
  val () = _names(dir, "big\n")
in _judge(dir, 1, "big: .github/workflows/big.yml: over the bound: the file is longer than the 524288 bytes", "1 over the bound", "", "pass, ") end

(* A file that is listed and also equals a template fails: exactly one holds *)
fn test_listed_and_template_fails (): bool = let
  val dir = "build/pin-audit-tests/both"
  val () = _fresh(dir)
  val () = _plant(dir, "both")
  val () = _fill(dir, "both", "publish.yml", "templates/publish.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "0", ~1)
  val () = _commit(dir, "both")
  val () = _names(dir, "both\n")
  val () = _allow(dir, "both/.github/workflows/publish.yml", "# Publishes this package to bats-lang/repository-prototype when src/ or\n# bats.toml changes on main. See PUBLISHING-SETUP.md there. Called by\n# commit, which the daily relock moves (bats-lang/repository-prototype#269).\nname: publish\non:\n  push:\n    branches: [main]\n    paths: ['src/**', 'bats.toml']\njobs:\n  publish:\n    uses: bats-lang/repository-prototype/.github/workflows/publish.yml@0123456789abcdef0123456789abcdef01234567 # repository-prototype main 0123456\n    secrets: inherit\n", "", "both#1")
in _judge(dir, 1, "both: .github/workflows/publish.yml: not canonical: its sha256 is listed in tools/pin-audit/allowlist.txt line 1 and it equals the template publish.yml", "drop the allowlist entry", "", "pass, ") end

(* A symbolic link named like a workflow fails *)
fn test_symbolic_link_fails (): bool = let
  val dir = "build/pin-audit-tests/symlink"
  val () = _fresh(dir)
  val () = _plant(dir, "link")
  val () = _workflow(dir, "link", "real.yml", "name: real\n")
  val _ = _run("ln", _l3(arg_text("-s"), arg_text("real.yml"), _join2(dir, "/planted/link.git/.github/workflows/link.yml")))
  val () = _commit(dir, "link")
  val () = _names(dir, "link\n")
in _judge(dir, 1, "link: .github/workflows/link.yml: not canonical: it is a symbolic link", "link.yml", "", "") end

(* A repository that cannot be cloned is an error of its own *)
fn test_missing_repository_fails (): bool = let
  val dir = "build/pin-audit-tests/missing"
  val () = _fresh(dir)
  val () = _names(dir, "missing\n")
in _judge(dir, 1, "::error title=pin audit::missing: cannot be cloned", "1 repository errors", "== failing repositories: missing", "") end

(* A name that is not a path-safe name is never put in a path *)
fn test_unsafe_name_fails (): bool = let
  val dir = "build/pin-audit-tests/unsafe-name"
  val () = _fresh(dir)
  val () = _names(dir, "../x\n")
in _judge(dir, 1, "::error title=pin audit::../x: the repository's name is not one the audit will put in a path", "1 repository errors", "", "cannot be cloned") end

(* A failing gh, a list longer than the buffer and an empty list fail the run *)
fn test_gh_failure_fails (): bool = let
  val dir = "build/pin-audit-tests/gh-fails"
  val () = _fresh(dir)
  val () = _flag(dir, "gh-fail")
in _judge(dir, 1, "the organisation's repositories could not be listed (gh status 1)", "", "", "== 0") end

fn test_gh_list_over_bound_fails (): bool = let
  val dir = "build/pin-audit-tests/gh-flood"
  val () = _fresh(dir)
  val () = _flag(dir, "gh-flood")
in _judge(dir, 1, "the list of the organisation's repositories is longer than the 524288 bytes", "", "", "== 0") end

fn test_empty_list_fails (): bool = let
  val dir = "build/pin-audit-tests/empty-list"
  val () = _fresh(dir)
in _judge(dir, 1, "the list held no repository", "", "", "") end

end
