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

(* dir/planted/name.git *)
fn _repo_arg {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): $P.arg_entry = let
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

(* dir/planted/name.git/rel *)
fn _repo_path {dir_len,name_len,rel_len,file_len:nat | dir_len < 200; name_len < 100; rel_len < 300; file_len < 300}
  (dir: string dir_len, name: string name_len, rel: string rel_len, file: string file_len): path_text = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/planted/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, ".git/")
  val () = $B.bput(out, rel)
  val () = $B.bput(out, file)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

fun _put_repeated {n:nat} .<n>. (rope: !$B.sized_rope, n: int n): void =
  if n <= 0 then ()
  else let
    val () = $B.sized_rope_put(rope, 97)
  in _put_repeated(rope, n - 1) end

(* ============================================================
   A case's directory
   ============================================================ *)

(* A fresh dir: the templates, the stand-in gh, an allowlist with no entry
   and an empty name list. The old one, if any, is removed first. *)
fn _fresh {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val _ = run_program("rm", args3(arg_text("-rf"), arg_text("--"), arg_text(dir)))
  val _ = run_program("mkdir", $L.list_vt_cons(arg_text("-p"), $L.list_vt_cons(arg_text("--"),
            args3(join_text2(dir, "/tools/pin-audit"), join_text2(dir, "/planted"), join_text2(dir, "/bin")))))
  val _ = run_program("cp", args3(arg_text("-R"), arg_text("templates"), join_text2(dir, "/tools/pin-audit/templates")))
  val _ = run_program("cp", args2(arg_text("dist/debug/gh_stand_in"), join_text2(dir, "/bin/gh")))
  var allowlist : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(allowlist, "# no entries\n")
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/allowlist.txt"), allowlist)
  var names : $B.sized_rope = $B.sized_rope_create()
  val _ = write_rope(join_path3(dir, "/", "gh-names.txt"), names)
in () end

(* The repository dir/planted/name.git, a new one, with no commit *)
fn _plant {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val _ = run_program("git", args3(arg_text("init"), arg_text("-q"), _repo_arg(dir, name)))
in () end

(* The repository's commit of everything written in it *)
fn _commit {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val _ = run_program("git", args4(arg_text("-C"), _repo_arg(dir, name), arg_text("add"), arg_text("-A")))
  val _ = run_program("git", $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_repo_arg(dir, name),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.name=plant"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.email=plant@example.com"),
            args4(arg_text("commit"), arg_text("-q"), arg_text("-m"), arg_text("plant")))))))))
in () end

(* The rope as a file of the planted repository, in folder rel (a
   directory is made) *)
fn _put_rope {dir_len,name_len,rel_len,file_len:nat | dir_len < 200; name_len < 100; rel_len < 300; file_len < 300}
  (dir: string dir_len, name: string name_len, rel: string rel_len, file: string file_len, text: $B.sized_rope): void = let
  val _ = run_program("mkdir", args3(arg_text("-p"), arg_text("--"), join_text2(dir, "/planted/")))
  var folder : $B.builder(0) = $B.create()
  val () = $B.bput(folder, dir)
  val () = $B.bput(folder, "/planted/")
  val () = $B.bput(folder, name)
  val () = $B.bput(folder, ".git/")
  val () = $B.bput(folder, rel)
  val @(folder_array, folder_len) = $B.to_arr(folder)
  val _ = run_program("mkdir", args3(arg_text("-p"), arg_text("--"), @(folder_array, folder_len)))
  val _ = write_rope(_repo_path(dir, name, rel, file), text)
in () end

(* The text of a file of the planted repository *)
fn _put {dir_len,name_len,rel_len,file_len,content_len:nat | dir_len < 200; name_len < 100; rel_len < 300; file_len < 300; content_len < 100000}
  (dir: string dir_len, name: string name_len, rel: string rel_len, file: string file_len, content: string content_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
in _put_rope(dir, name, rel, file, text) end

(* A workflow file of the planted repository *)
fn _workflow {dir_len,name_len,file_len,content_len:nat | dir_len < 200; name_len < 100; file_len < 300; content_len < 100000}
  (dir: string dir_len, name: string name_len, file: string file_len, content: string content_len): void =
  _put(dir, name, ".github/workflows/", file, content)

fun _fill_loop {l:agz}{template_len:nat | template_len <= 524288}{template_at:nat | template_at <= template_len}{commit_len,comment_len,minute_len:nat} .<template_len - template_at>.
  (template_text: !$A.borrow(byte, l, 524288), template_len: int template_len, template_at: int template_at, out: !$B.sized_rope,
   commit: string commit_len, comment: string comment_len, minute: string minute_len, mutate: int): void = let
  val commit_end = lit_step(template_text, template_len, template_at, "@@COMMIT@@")
in
  if commit_end >= 0 then let
    val () = $B.sized_rope_bput(out, commit)
  in _fill_loop(template_text, template_len, commit_end, out, commit, comment, minute, mutate) end
  else let
    val comment_end = lit_step(template_text, template_len, template_at, "@@COMMENT@@")
  in
    if comment_end >= 0 then let
      val () = $B.sized_rope_bput(out, comment)
    in _fill_loop(template_text, template_len, comment_end, out, commit, comment, minute, mutate) end
    else let
      val minute_end = lit_step(template_text, template_len, template_at, "@@MINUTE@@")
    in
      if minute_end >= 0 then let
        val () = $B.sized_rope_bput(out, minute)
      in _fill_loop(template_text, template_len, minute_end, out, commit, comment, minute, mutate) end
      else if template_at >= template_len then ()
      else let
        val byte_value = byte2int0($A.read<byte>(template_text, template_at))
        val () = $B.sized_rope_put(out, $AR.low_byte(if template_at = mutate then 126 else byte_value))
      in _fill_loop(template_text, template_len, template_at + 1, out, commit, comment, minute, mutate) end
    end
  end
end

(* The template at template_path with its holes filled with the values
   (mutate: the place of one byte of a segment changed to `~`, or ~1), as
   a workflow file of the planted repository *)
fn _fill {dir_len,name_len,file_len,template_path_len,commit_len,comment_len,minute_len:nat | dir_len < 200; name_len < 100; file_len < 300; template_path_len < 4096}
  (dir: string dir_len, name: string name_len, file: string file_len, template_path: string template_path_len,
   commit: string commit_len, comment: string comment_len, minute: string minute_len, mutate: int): void = let
  var template : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant(template_path, template)
  val @(template_array, template_len) = $B.to_arr(template)
  val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = _fill_loop(template_view, template_len, 0, text, commit, comment, minute, mutate)
  val () = $A.drop<byte>(template_frozen, template_view)
  val () = $A.free<byte>($A.thaw<byte>(template_frozen))
in _put_rope(dir, name, ".github/workflows/", file, text) end

(* The sha256 of the text, as 64 digits, appended to the rope *)
fn _hash_into {content_len:nat | content_len < 100000} (text: !$B.sized_rope, content: string content_len): void = let
  var body : $B.builder(0) = $B.create()
  val () = $B.bput(body, content)
  val @(arr, k) = $B.to_arr(body)
  val hex = sha256_hex(arr, k)
  val () = $A.free<byte>(arr)
  val @(hash_frozen, hash_view) = $A.freeze<byte>(hex)
  val () = $B.sized_rope_copy(text, hash_view, 0, 64)
  val () = $A.drop<byte>(hash_frozen, hash_view)
  val () = $A.free<byte>($A.thaw<byte>(hash_frozen))
in () end

(* The allowlist of the case: one entry, the key, the sha256 of the first
   content, the sha256 of the second when it is not empty, and ` # ` and
   the comment when it is not empty *)
fn _allow {dir_len,key_len,first_len,second_len,comment_len:nat | dir_len < 200; key_len < 1000; first_len < 100000; second_len < 100000; comment_len < 1000}
  (dir: string dir_len, key: string key_len, first: string first_len, second: string second_len, comment: string comment_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, key)
  val () = $B.sized_rope_bput(text, " ")
  val () = _hash_into(text, first)
  val () =
    if text_length(second) > 0 then let
      val () = $B.sized_rope_bput(text, " ")
    in _hash_into(text, second) end
    else ()
  val () =
    if text_length(comment) > 0 then let
      val () = $B.sized_rope_bput(text, " # ")
    in $B.sized_rope_bput(text, comment) end
    else ()
  val () = $B.sized_rope_bput(text, "\n")
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/allowlist.txt"), text)
in () end

(* The allowlist of the case, as written *)
fn _allow_raw {dir_len,content_len:nat | dir_len < 200; content_len < 100000} (dir: string dir_len, content: string content_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/allowlist.txt"), text)
in () end

(* The names gh prints, one on each line *)
fn _names {dir_len,content_len:nat | dir_len < 200; content_len < 100000} (dir: string dir_len, content: string content_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = write_rope(join_path3(dir, "/", "gh-names.txt"), text)
in () end

(* A file of the case (an empty one: gh-fail makes the stand-in exit 1,
   gh-flood makes it print more than the audit reads) *)
fn _flag {dir_len,file_len:nat | dir_len < 200; file_len < 300} (dir: string dir_len, file: string file_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val _ = write_rope(join_path3(dir, "/", file), text)
in () end

(* gitconfig of the case: https://github.com/bats-lang/ is the directory of
   its planted repositories (url.<dir>.insteadOf) *)
fn _config {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val cwd = $A.alloc<byte>(4096)
  val cwd_len = cwd_length(cwd)
  val @(cwd_frozen, cwd_view) = $A.freeze<byte>(cwd)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, "[url \"file://")
  val () = $B.sized_rope_copy(text, cwd_view, 0, cwd_len)
  val () = $B.sized_rope_bput(text, "/")
  val () = $B.sized_rope_bput(text, dir)
  val () = $B.sized_rope_bput(text, "/planted/\"]\n\tinsteadOf = https://github.com/bats-lang/\n")
  val _ = write_rope(join_path3(dir, "/", "gitconfig"), text)
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in () end

(* ============================================================
   Running the audit
   ============================================================ *)

(* The built audit in dir, with the stand-in gh first on PATH and the
   planted repositories behind GIT_CONFIG_GLOBAL: its exit status, its
   output in out *)
fn _audit {dir_len:nat | dir_len < 200} (dir: string dir_len, out: !$B.builder(0) >> $B.builder_v): @(int, read_end) = let
  val () = _config(dir)
  val cwd = $A.alloc<byte>(4096)
  val cwd_len = cwd_length(cwd)
  val @(cwd_frozen, cwd_view) = $A.freeze<byte>(cwd)
  var pname : $B.builder(0) = $B.create()
  val () = $B.bput(pname, "PATH")
  val @(variable_array, _) = $B.to_arr(pname)
  val old = $A.alloc<byte>(8192)
  val old_path_len = (case+ $E.get_cstr(variable_array, 524288, old, 8192) of | ~$R.some(k) => k | ~$R.none() => 0): [k:nat | k <= 8192] int k
  val () = $A.free<byte>(variable_array)
  val @(old_frozen, old_view) = $A.freeze<byte>(old)
  var path_entry : $B.builder(0) = $B.create()
  val () = $B.bput(path_entry, "PATH=")
  val () = put_range(cwd_view, 0, cwd_len, path_entry)
  val () = $B.bput(path_entry, "/")
  val () = $B.bput(path_entry, dir)
  val () = $B.bput(path_entry, "/bin:")
  val () = put_range(old_view, 0, old_path_len, path_entry)
  val @(path_entry_array, path_entry_len) = $B.to_arr(path_entry)
  var config_entry : $B.builder(0) = $B.create()
  val () = $B.bput(config_entry, "GIT_CONFIG_GLOBAL=")
  val () = put_range(cwd_view, 0, cwd_len, config_entry)
  val () = $B.bput(config_entry, "/")
  val () = $B.bput(config_entry, dir)
  val () = $B.bput(config_entry, "/gitconfig")
  val @(config_entry_array, config_entry_len) = $B.to_arr(config_entry)
  val result = capture_with("env",
    args4(arg_text("env"), arg_text("-C"), arg_text(dir), arg_text("../../../dist/debug/pin_audit")),
    args2(@(path_entry_array, path_entry_len), @(config_entry_array, config_entry_len)), out)
  val () = $A.drop<byte>(old_frozen, old_view)
  val () = $A.free<byte>($A.thaw<byte>(old_frozen))
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in result end

(* Runs the case and judges it: the exit status is want, the output holds
   the three texts and lacks the last. A failing case prints what it saw. *)
fn _judge {dir_len,first_len,second_len,third_len,absent_len:nat | dir_len < 200}
  (dir: string dir_len, want: int, first: string first_len, second: string second_len, third: string third_len, absent: string absent_len): bool = let
  var out : $B.builder(0) = $B.create()
  val @(status, ended) = _audit(dir, out)
  val @(output_array, output_len) = $B.to_arr(out)
  val @(output_frozen, output_view) = $A.freeze<byte>(output_array)
  val whole = (case+ ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
  val good = whole && status = want && output_has(output_view, output_len, first) && output_has(output_view, output_len, second) && output_has(output_view, output_len, third) && output_lacks(output_view, output_len, absent): bool
  val () =
    if good then ()
    else let
      val () = println! ("FAIL ", dir, ": exit status ", status, " (wanted ", want, "), the output was read whole: ", whole)
      val () = println! ("  wanted: ", first, " | ", second, " | ", third, " | and lacking: ", absent)
      val () = println! ("  the audit's output:")
      val () = print_range(output_view, 0, output_len)
    in println! ("  (the case's directory ", dir, " is kept)") end
  val () = $A.drop<byte>(output_frozen, output_view)
  val () = $A.free<byte>($A.thaw<byte>(output_frozen))
in good end

(* ============================================================
   The templates' holes, in the matcher
   ============================================================ *)

(* Whether the file is the template, each as a text of its own *)
fn _matches {template_string_len,file_string_len:nat | template_string_len < 4096; file_string_len < 4096} (template: string template_string_len, file: string file_string_len): bool = let
  var template_builder : $B.builder(0) = $B.create()
  val () = $B.bput(template_builder, template)
  val @(template_array, template_len) = $B.to_arr(template_builder)
  var file_builder : $B.builder(0) = $B.create()
  val () = $B.bput(file_builder, file)
  val @(file_array, file_len) = $B.to_arr(file_builder)
  val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
  val @(file_frozen, file_view) = $A.freeze<byte>(file_array)
  val result = template_matches(template_view, template_len, file_view, file_len)
  val () = $A.drop<byte>(file_frozen, file_view)
  val () = $A.free<byte>($A.thaw<byte>(file_frozen))
  val () = $A.drop<byte>(template_frozen, template_view)
  val () = $A.free<byte>($A.thaw<byte>(template_frozen))
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

(* The comment `canonical` names no ticket: every entry names the p2 ticket
   that says to fix its file, so the entry fails the audit *)
fn test_canonical_comment_fails (): bool = let
  val dir = "build/pin-audit-tests/canonical-comment"
  val () = _fresh(dir)
  val () = _plant(dir, "bespoke")
  val () = _workflow(dir, "bespoke", "own.yml", "name: own\non: push\n")
  val () = _commit(dir, "bespoke")
  val () = _names(dir, "bespoke\n")
  val () = _allow(dir, "bespoke/.github/workflows/own.yml", "name: own\non: push\n", "", "canonical")
in _judge(dir, 1, "allowlist.txt line 1: it has no ticket comment", "bespoke: .github/workflows/own.yml: not canonical", "1 entries, 1 failing", "pass, its") end

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
  val _ = run_program("ln", args3(arg_text("-s"), arg_text("real.yml"), join_text2(dir, "/planted/link.git/.github/workflows/link.yml")))
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
