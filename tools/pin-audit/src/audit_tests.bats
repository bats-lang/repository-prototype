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

(* A fresh dir: a git repository with one commit (made with fixed names and dates, so its
   hash is the same on every run: the commit the audit puts in a ticket), the templates, the
   stand-in gh, an allowlist with no entry and an empty name list. The old one, if any, is
   removed first. *)
fn _fresh {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val _ = run_program("rm", args3(arg_text("-rf"), arg_text("--"), arg_text(dir)))
  val _ = run_program("mkdir", $L.list_vt_cons(arg_text("-p"), $L.list_vt_cons(arg_text("--"),
            args3(join_text2(dir, "/tools/pin-audit"), join_text2(dir, "/planted"), join_text2(dir, "/bin")))))
  val _ = run_program("cp", args3(arg_text("-R"), arg_text("templates"), join_text2(dir, "/tools/pin-audit/templates")))
  val _ = run_program("cp", args2(arg_text("dist/debug/gh_stand_in"), join_text2(dir, "/bin/gh")))
  val _ = run_program("git", args3(arg_text("init"), arg_text("-q"), arg_text(dir)))
  val _ = run_with("git", $L.list_vt_cons(arg_text("git"), $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(arg_text(dir),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.name=plant"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.email=plant@example.com"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("commit.gpgsign=false"),
            $L.list_vt_cons(arg_text("commit"), $L.list_vt_cons(arg_text("-q"), $L.list_vt_cons(arg_text("--allow-empty"),
            args2(arg_text("-m"), arg_text("plant")))))))))))))),
            args2(arg_text("GIT_AUTHOR_DATE=2026-01-01T00:00:00+0000"), arg_text("GIT_COMMITTER_DATE=2026-01-01T00:00:00+0000")))
  var allowlist : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(allowlist, "# no entries\n")
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/allowlist.txt"), allowlist)
  var skip_list : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(skip_list, "# no entries\n")
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/skipped.txt"), skip_list)
  var names : $B.sized_rope = $B.sized_rope_create()
  val _ = write_rope(join_path3(dir, "/", "gh-names.txt"), names)
in () end

(* The skip list of the case, as written *)
fn _skip_raw {dir_len,content_len:nat | dir_len < 200; content_len < 100000} (dir: string dir_len, content: string content_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = write_rope(join_path3(dir, "/", "tools/pin-audit/skipped.txt"), text)
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

(* The built audit in dir with the options (its arguments), with the stand-in gh first on PATH, the
   planted repositories behind GIT_CONFIG_GLOBAL and the entry token (GH_TOKEN=<value>, empty for
   no token) in its environment: its exit status, its output in out *)
fn _audit_run {dir_len,token_len:nat | dir_len < 200; token_len < 200}
  (dir: string dir_len, options: $L.listv($P.arg_entry), token: string token_len, out: !$B.builder(0) >> $B.builder_v): @(int, read_end) = let
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
    $L.list_vt_cons(arg_text("env"), $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(arg_text(dir),
      $L.list_vt_cons(arg_text("../../../dist/debug/pin_audit"), options)))),
    $L.list_vt_cons(arg_text(token), args2(@(path_entry_array, path_entry_len), @(config_entry_array, config_entry_len))), out)
  val () = $A.drop<byte>(old_frozen, old_view)
  val () = $A.free<byte>($A.thaw<byte>(old_frozen))
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in result end

(* The audit with no option and no token *)
fn _audit {dir_len:nat | dir_len < 200} (dir: string dir_len, out: !$B.builder(0) >> $B.builder_v): @(int, read_end) =
  _audit_run(dir, no_arguments(), "GH_TOKEN=", out)

(* Runs the case with the options and the token and judges it: the exit status is want, the output holds
   the three texts and lacks the last. A failing case prints what it saw. *)
fn _judge_run {dir_len,token_len,first_len,second_len,third_len,absent_len:nat | dir_len < 200; token_len < 200}
  (dir: string dir_len, options: $L.listv($P.arg_entry), token: string token_len,
   want: int, first: string first_len, second: string second_len, third: string third_len, absent: string absent_len): bool = let
  var out : $B.builder(0) = $B.create()
  val @(status, ended) = _audit_run(dir, options, token, out)
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

(* ... with no option and no token *)
fn _judge {dir_len,first_len,second_len,third_len,absent_len:nat | dir_len < 200}
  (dir: string dir_len, want: int, first: string first_len, second: string second_len, third: string third_len, absent: string absent_len): bool =
  _judge_run(dir, no_arguments(), "GH_TOKEN=", want, first, second, third, absent)

(* The file file of the case's directory read into out *)
fn _read_file_of {dir_len,file_len:nat | dir_len < 200; file_len < 200}
  (dir: string dir_len, file: string file_len, out: !$B.builder(0) >> $B.builder_v): @(read_end, string) = let
  val @(path_array, path_len) = join_path3(dir, "/", file)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val read = read_file(path_view, path_len, out)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in read end

(* Whether the file of the case's directory holds the first text and lacks the second (a file that is not there is empty) *)
fn _file_judge {dir_len,file_len,has_len,lacks_len:nat | dir_len < 200; file_len < 200}
  (dir: string dir_len, file: string file_len, has: string has_len, lacks: string lacks_len): bool = let
  var text : $B.builder(0) = $B.create()
  val @(ended, _) = _read_file_of(dir, file, text)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val read_ok = (case+ ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => text_length(has) = 0): bool
  val good = read_ok && output_has(text_view, text_len, has) && output_lacks(text_view, text_len, lacks)
  val () =
    if good then ()
    else let
      val () = println! ("FAIL ", dir, "/", file, ": wanted it to hold: ", has, " | and lack: ", lacks)
      val () = println! ("  it was:")
    in print_range(text_view, 0, text_len) end
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in good end

(* The text a ticket's body has for the file path (in backquotes) whose template is template_path, filled
   with the values: written to the rope. The test's own copy of the body's form, so the audit's is
   compared with a text that is not its code. *)
fn _expect_section {path_len,template_path_len,commit_len,comment_len,minute_len:nat | path_len < 100; template_path_len < 4096}
  (body: !$B.sized_rope, path: string path_len, template_path: string template_path_len,
   commit: string commit_len, comment: string comment_len, minute: string minute_len): void = let
  val () = $B.sized_rope_bput(body, "## `")
  val () = $B.sized_rope_bput(body, path)
  val () = $B.sized_rope_bput(body, "`\n\nThe audit compares bytes: the file is exactly this text.\n\n```\n")
  var template : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant(template_path, template)
  val @(template_array, template_len) = $B.to_arr(template)
  val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
  val () = _fill_loop(template_view, template_len, 0, body, commit, comment, minute, ~1)
  val () = $A.drop<byte>(template_frozen, template_view)
  val () = $A.free<byte>($A.thaw<byte>(template_frozen))
in $B.sized_rope_bput(body, "```\n\n") end

(* The start of every ticket's body *)
fn _expect_start (body: !$B.sized_rope): void =
  $B.sized_rope_bput(body, "These files are neither listed by sha256 in tools/pin-audit/allowlist.txt of bats-lang/repository-prototype nor equal to a template there with its holes filled. The correct file is shown for each.\n\n")

(* The end of the body of the ticket of the repository repository *)
fn _expect_end {repository_len:nat | repository_len < 100} (body: !$B.sized_rope, repository: string repository_len): void = let
  val () = $B.sized_rope_bput(body, "Done when: `pin_audit --repository ")
  val () = $B.sized_rope_bput(body, repository)
in $B.sized_rope_bput(body, "` exits 0.\n") end

(* The path of the body the audit wrote for the repository, as an argument *)
fn _actual_body_arg {dir_len,repository_len:nat | dir_len < 100; repository_len < 100}
  (dir: string dir_len, repository: string repository_len): $P.arg_entry = let
  var actual_path : $B.builder(0) = $B.create()
  val () = $B.bput(actual_path, dir)
  val () = $B.bput(actual_path, "/audit-clones/")
  val () = $B.bput(actual_path, repository)
  val () = $B.bput(actual_path, ".ticket.md")
  val @(actual_array, actual_len) = $B.to_arr(actual_path)
in @(actual_array, actual_len) end

(* Whether the body the audit wrote for the repository (audit-clones/<repository>.ticket.md of the case's directory)
   is byte for byte the expected text; a difference is shown *)
fn _body_is {dir_len,repository_len:nat | dir_len < 100; repository_len < 100}
  (dir: string dir_len, repository: string repository_len, expected: $B.sized_rope): bool = let
  val _ = write_rope(join_path3(dir, "/", "expected-body.md"), expected)
  val same = run_program("cmp", args3(arg_text("-s"), join_text2(dir, "/expected-body.md"), _actual_body_arg(dir, repository)))
  val () =
    if same = 0 then ()
    else let
      val () = println! ("FAIL ", dir, ": the ticket's body is not the expected text; diff expected actual:")
      val _ = run_program("diff", args2(join_text2(dir, "/expected-body.md"), _actual_body_arg(dir, repository)))
    in () end
in same = 0 end

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

(* A repository with no CI input at all fails, named: bats check-pins --discover exits 2 for it, and a
   nonzero exit is a failure of the repository *)
fn test_repository_without_workflows_fails (): bool = let
  val dir = "build/pin-audit-tests/no-workflows"
  val () = _fresh(dir)
  val () = _plant(dir, "quiet")
  val () = _put(dir, "quiet", "", "README.md", "nothing here\n")
  val () = _commit(dir, "quiet")
  val () = _names(dir, "quiet\n")
in _judge(dir, 1, "::error title=pin audit::quiet: bats check-pins --discover failed (status 2)", "1 repositories, 0 workflow files", "1 repository errors", "pass, ") end

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

(* ============================================================
   --repository (bats-lang/repository-prototype#405)
   ============================================================ *)

(* The options `--repository <name>` *)
fn _only {name_len:nat | name_len < 100} (name: string name_len): $L.listv($P.arg_entry) =
  args2(arg_text("--repository"), arg_text(name))

(* A repository whose one file is a canonical check.yml *)
fn _plant_fine {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val () = _plant(dir, name)
  val () = _fill(dir, name, "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
in _commit(dir, name) end

(* A repository whose one file is a check.yml that is not canonical *)
fn _plant_diverging {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val () = _plant(dir, name)
  val () = _workflow(dir, name, "check.yml", "name: my own check\non: push\n")
in _commit(dir, name) end

(* --repository audits that repository alone, passing: the stand-in gh fails if it is asked for a list, and the list names another *)
fn test_repository_option_passes (): bool = let
  val dir = "build/pin-audit-tests/only-passes"
  val () = _fresh(dir)
  val () = _plant_fine(dir, "fine")
  val () = _plant_diverging(dir, "other")
  val () = _names(dir, "other\nfine\n")
  val () = _flag(dir, "gh-fail")
in _judge_run(dir, _only("fine"), "GH_TOKEN=", 0, "== fine\n", "1 repositories, 1 workflow files", ".github/workflows/check.yml: pass, equal to the template check.yml", "other") end

(* ... failing, with the repository named and no other *)
fn test_repository_option_fails (): bool = let
  val dir = "build/pin-audit-tests/only-fails"
  val () = _fresh(dir)
  val () = _plant_fine(dir, "fine")
  val () = _plant_diverging(dir, "bad")
  val () = _names(dir, "fine\nbad\n")
  val () = _flag(dir, "gh-fail")
in _judge_run(dir, _only("bad"), "GH_TOKEN=", 1, "::error title=pin audit::bad: .github/workflows/check.yml: not canonical", "1 repositories, 1 workflow files", "== failing repositories: bad", "fine") end

(* Without the option every repository of the stand-in gh's list is audited *)
fn test_without_option_audits_every_repository (): bool = let
  val dir = "build/pin-audit-tests/every"
  val () = _fresh(dir)
  val () = _plant_fine(dir, "fine")
  val () = _plant_diverging(dir, "bad")
  val () = _names(dir, "fine\nbad\n")
in _judge(dir, 1, "== fine\n", "== bad\n", "== 2 repositories, 2 workflow files: 0 passed by an allowlisted hash, 1 passed by a template, 1 not canonical, 0 over the bound, 0 unreadable; 0 repository errors", "") end

(* Arguments that are not the options are refused with status 2, and nothing is audited *)
fn test_unknown_option_refused (): bool = let
  val dir = "build/pin-audit-tests/option-unknown"
  val () = _fresh(dir)
in _judge_run(dir, args1(arg_text("--bogus")), "GH_TOKEN=", 2, "usage: pin_audit [--repository <name>] [--file-tickets]", "", "", "== ") end

fn test_repository_without_name_refused (): bool = let
  val dir = "build/pin-audit-tests/option-no-name"
  val () = _fresh(dir)
in _judge_run(dir, args1(arg_text("--repository")), "GH_TOKEN=", 2, "usage: pin_audit", "", "", "== ") end

fn test_repository_twice_refused (): bool = let
  val dir = "build/pin-audit-tests/option-twice"
  val () = _fresh(dir)
in _judge_run(dir, args4(arg_text("--repository"), arg_text("a"), arg_text("--repository"), arg_text("b")), "GH_TOKEN=", 2, "usage: pin_audit", "", "", "== ") end

(* ============================================================
   bats check-pins --discover (bats-lang/repository-prototype#405)
   ============================================================ *)

(* A repository that passes says that the checker ran in its clone *)
fn test_checker_runs_in_the_clone (): bool = let
  val dir = "build/pin-audit-tests/checker-runs"
  val () = _fresh(dir)
  val () = _plant_fine(dir, "fine")
in _judge_run(dir, _only("fine"), "GH_TOKEN=", 0, "== fine\n   bats check-pins --discover:\n", "0 repository errors", "", "failed") end

(* A clone with a floating input fails with the repository named and the checker's own failure under it, though
   the file is listed (so the file audit passes and the checker is the only failure) *)
fn test_floating_input_fails (): bool = let
  val dir = "build/pin-audit-tests/floating"
  val () = _fresh(dir)
  val () = _plant(dir, "floating")
  val () = _workflow(dir, "floating", "own.yml", "name: own\non: push\njobs:\n  build:\n    runs-on: ubuntu-latest\n")
  val () = _commit(dir, "floating")
  val () = _allow(dir, "floating/.github/workflows/own.yml", "name: own\non: push\njobs:\n  build:\n    runs-on: ubuntu-latest\n", "", "floating#1")
in _judge_run(dir, _only("floating"), "GH_TOKEN=", 1, "::error title=pin audit::floating: bats check-pins --discover failed (status 1)",
     ".github/workflows/own.yml:5:", "1 repository errors", "not canonical:") end

(* ============================================================
   The ticket of a diverging repository (bats-lang/repository-prototype#405)
   ============================================================ *)

(* The options `--repository <name> --file-tickets` *)
fn _only_with_tickets {name_len:nat | name_len < 100} (name: string name_len): $L.listv($P.arg_entry) =
  args3(arg_text("--repository"), arg_text(name), arg_text("--file-tickets"))

(* A repository with two offending files: a check.yml and a relock.yml (cron minute 41) that are neither listed nor templates *)
fn _plant_two_offenders {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val () = _plant(dir, name)
  val () = _workflow(dir, name, "check.yml", "name: my own check\non: push\n")
  val () = _workflow(dir, name, "relock.yml", "name: relock\non:\n  schedule:\n    - cron: '41 5 * * *'\n")
in _commit(dir, name) end

(* The body of the ticket for _plant_two_offenders: the check.yml and the relock.yml of the templates with the checkout's commit
   (the case's directory has one fixed commit), its comment and the repository's own minute 41 *)
fn _expect_two_offenders {name_len:nat | name_len < 100} (name: string name_len): $B.sized_rope = let
  var body : $B.sized_rope = $B.sized_rope_create()
  val () = _expect_start(body)
  val () = _expect_section(body, ".github/workflows/check.yml", "templates/check.yml", "8a556d1e80eed22883318e2c6d9a1c7c299ca140", "repository-prototype main 8a556d1", "41")
  val () = _expect_section(body, ".github/workflows/relock.yml", "templates/relock.yml", "8a556d1e80eed22883318e2c6d9a1c7c299ca140", "repository-prototype main 8a556d1", "41")
  val () = _expect_end(body, name)
in body end

(* Two offending files: one created ticket, titled by the repository, labelled p0, whose body has each file's path and its
   whole correct text; the open tickets were listed first, and nothing was edited *)
fn test_two_offenders_get_one_created_ticket (): bool = let
  val dir = "build/pin-audit-tests/ticket-created"
  val () = _fresh(dir)
  val () = _plant_two_offenders(dir, "diverge")
  val judged = _judge_run(dir, _only_with_tickets("diverge"), "GH_TOKEN=test-token", 1,
    "   ticket created: https://example.invalid/create\n", "== 1 repositories, 2 workflow files: 0 passed by an allowlisted hash, 0 passed by a template, 2 not canonical", "== failing repositories: diverge", "ticket updated")
  val listed = _file_judge(dir, "gh-calls.txt", "gh issue list -R bats-lang/diverge --state open --limit 100 --search Make diverge's workflow and issue-template files canonical in:title --json number,title --jq", "issue edit")
  val created = _file_judge(dir, "gh-calls.txt", "gh issue create -R bats-lang/diverge --title Make diverge's workflow and issue-template files canonical --label p0 --body-file audit-clones/diverge.ticket.md\n", "issue edit")
  val body = _body_is(dir, "diverge", _expect_two_offenders("diverge"))
in judged && listed && created && body end

(* A ticket of the title that is open gets its body replaced: one edit, no create, the same body *)
fn test_open_ticket_is_edited (): bool = let
  val dir = "build/pin-audit-tests/ticket-edited"
  val () = _fresh(dir)
  val () = _plant_two_offenders(dir, "diverge")
  val () = _put(dir, "diverge", "", "unrelated.txt", "x\n")
  val _ = write_rope(join_path3(dir, "/", "gh-open.txt"), let var open : $B.sized_rope = $B.sized_rope_create() val () = $B.sized_rope_bput(open, "7\n") in open end)
  val judged = _judge_run(dir, _only_with_tickets("diverge"), "GH_TOKEN=test-token", 1,
    "   ticket updated: https://example.invalid/edit\n", "2 not canonical", "== failing repositories: diverge", "ticket created")
  val edited = _file_judge(dir, "gh-calls.txt", "gh issue edit 7 -R bats-lang/diverge --body-file audit-clones/diverge.ticket.md\n", "issue create")
  val body = _body_is(dir, "diverge", _expect_two_offenders("diverge"))
in judged && edited && body end

(* A repository that passes gets no ticket: gh is not called for one *)
fn test_passing_repository_gets_no_ticket (): bool = let
  val dir = "build/pin-audit-tests/ticket-none"
  val () = _fresh(dir)
  val () = _plant_fine(dir, "fine")
  val judged = _judge_run(dir, _only_with_tickets("fine"), "GH_TOKEN=test-token", 0, "== fine\n", "1 passed by a template", "", "ticket created")
  val none = _file_judge(dir, "gh-calls.txt", "", "issue")
in judged && none end

(* A missing token (GH_TOKEN empty, as the workflow's secret is when it is not set) exits 1 with a message naming AUDIT_TOKEN,
   audits nothing and calls gh for nothing *)
fn test_missing_token_files_nothing (): bool = let
  val dir = "build/pin-audit-tests/ticket-no-token"
  val () = _fresh(dir)
  val () = _plant_two_offenders(dir, "diverge")
  val judged = _judge_run(dir, _only_with_tickets("diverge"), "GH_TOKEN=", 1,
    "::error title=pin audit::AUDIT_TOKEN is missing", "nothing was filed", "", "== ")
  val none = _file_judge(dir, "gh-calls.txt", "", "issue")
in judged && none end

(* The minute is 17 when the offending relock.yml has no cron line, and a file with no template of its name says so, with its hash *)
fn test_minute_seventeen_and_file_without_template (): bool = let
  val dir = "build/pin-audit-tests/ticket-seventeen"
  val () = _fresh(dir)
  val () = _plant(dir, "odd")
  val () = _workflow(dir, "odd", "relock.yml", "name: relock\non: push\n")
  val () = _workflow(dir, "odd", "deploy.yml", "name: deploy\non: push\n")
  val () = _commit(dir, "odd")
  val judged = _judge_run(dir, _only_with_tickets("odd"), "GH_TOKEN=test-token", 1, "ticket created", "2 not canonical", "", "ticket updated")
  var expected : $B.sized_rope = $B.sized_rope_create()
  val () = _expect_start(expected)
  val () = $B.sized_rope_bput(expected, "## `.github/workflows/deploy.yml`\n\nNo template of this name is in tools/pin-audit/templates of bats-lang/repository-prototype, so the file has no correct text to show. Delete it, or list its sha256 ")
  val () = _hash_into(expected, "name: deploy\non: push\n")
  val () = $B.sized_rope_bput(expected, " in tools/pin-audit/allowlist.txt there with a ticket comment.\n\n")
  val () = _expect_section(expected, ".github/workflows/relock.yml", "templates/relock.yml", "8a556d1e80eed22883318e2c6d9a1c7c299ca140", "repository-prototype main 8a556d1", "17")
  val () = _expect_end(expected, "odd")
  val body = _body_is(dir, "odd", expected)
in judged && body end

(* A symbolic link has no sha256 to list: its section says to delete it *)
fn test_symbolic_link_section_says_delete (): bool = let
  val dir = "build/pin-audit-tests/ticket-symlink"
  val () = _fresh(dir)
  val () = _plant(dir, "link")
  val () = _workflow(dir, "link", "real.yml", "name: real\n")
  val _ = run_program("ln", args3(arg_text("-s"), arg_text("real.yml"), join_text2(dir, "/planted/link.git/.github/workflows/link.yml")))
  val () = _commit(dir, "link")
  val () = _allow(dir, "link/.github/workflows/real.yml", "name: real\n", "", "link#1")
  val judged = _judge_run(dir, _only_with_tickets("link"), "GH_TOKEN=test-token", 1, "ticket created", "1 not canonical", "", "ticket updated")
  var expected : $B.sized_rope = $B.sized_rope_create()
  val () = _expect_start(expected)
  val () = $B.sized_rope_bput(expected, "## `.github/workflows/link.yml`\n\nNo template of this name is in tools/pin-audit/templates of bats-lang/repository-prototype, so the file has no correct text to show. Delete it.\n\n")
  val () = _expect_end(expected, "link")
  val body = _body_is(dir, "link", expected)
in judged && body end

(* ============================================================
   The skip list (bats-lang/repository-prototype#430)
   ============================================================ *)

(* A repository named in tools/pin-audit/skipped.txt is not cloned and gets no ticket, though its file is not canonical; an
   unlisted one with a non-canonical file still fails and gets its ticket; the summary line names the skipped one *)
fn test_skipped_repository_is_neither_cloned_nor_ticketed (): bool = let
  val dir = "build/pin-audit-tests/skip-listed"
  val () = _fresh(dir)
  val () = _plant_diverging(dir, "relock-scratch")
  val () = _plant_diverging(dir, "bad")
  val () = _names(dir, "relock-scratch\nbad\n")
  val () = _skip_raw(dir, "# test\nrelock-scratch a fixture that is non-canonical on purpose\n")
  val judged = _judge_run(dir, args1(arg_text("--file-tickets")), "GH_TOKEN=test-token", 1,
    "== relock-scratch: skipped, listed in tools/pin-audit/skipped.txt (not cloned, no ticket)\n",
    "bad: .github/workflows/check.yml: not canonical",
    "1 not canonical, 0 over the bound, 0 unreadable; 0 repository errors; skipped (tools/pin-audit/skipped.txt): 1 relock-scratch\n== allowlist:",
    "relock-scratch: .github")
  val ticketed = _file_judge(dir, "gh-calls.txt", "issue create -R bats-lang/bad ", "relock-scratch")
  val not_cloned = (~constant_exists("build/pin-audit-tests/skip-listed/audit-clones/relock-scratch/.git/HEAD")): bool
  val cloned_other = constant_exists("build/pin-audit-tests/skip-listed/audit-clones/bad/.git/HEAD")
in judged && ticketed && not_cloned && cloned_other end

(* A skipped repository named by --repository is skipped too, and the run passes *)
fn test_skipped_repository_named_alone_passes (): bool = let
  val dir = "build/pin-audit-tests/skip-alone"
  val () = _fresh(dir)
  val () = _plant_diverging(dir, "relock-scratch")
  val () = _skip_raw(dir, "relock-scratch a fixture that is non-canonical on purpose\n")
  val judged = _judge_run(dir, _only("relock-scratch"), "GH_TOKEN=", 0, "== relock-scratch: skipped", "skipped (tools/pin-audit/skipped.txt): 1 relock-scratch", "skip list: 1 entries, 0 failing", ": not canonical")
  val not_cloned = (~constant_exists("build/pin-audit-tests/skip-alone/audit-clones/relock-scratch/.git/HEAD")): bool
in judged && not_cloned end

(* Names are exact: an entry for a prefix skips nothing else, and a run that skips nothing says so *)
fn test_skip_list_names_are_exact (): bool = let
  val dir = "build/pin-audit-tests/skip-exact"
  val () = _fresh(dir)
  val () = _plant_diverging(dir, "relock-scratch")
  val () = _names(dir, "relock-scratch\n")
  val () = _skip_raw(dir, "relock a prefix is not the name\nrelock-scratch-2 nor is a longer name\n")
in _judge(dir, 1, "relock-scratch: .github/workflows/check.yml: not canonical", "repository errors; skipped (tools/pin-audit/skipped.txt): 0\n", "2 entries, 0 failing", "skipped, listed") end

(* A line of the skip list with no reason, or that is not an entry, fails the audit and skips nothing *)
fn test_malformed_skip_list_fails (): bool = let
  val dir = "build/pin-audit-tests/skip-malformed"
  val () = _fresh(dir)
  val () = _plant_diverging(dir, "relock-scratch")
  val () = _names(dir, "relock-scratch\n")
  val () = _skip_raw(dir, "relock-scratch\n/bad name\n")
in _judge(dir, 1, "skipped.txt line 1: it has no reason after the name", "skipped.txt line 2: it does not start with a repository name", "skip list: 2 entries, 2 failing", "skipped, listed") end

(* ============================================================
   .github/ISSUE_TEMPLATE (bats-lang/repository-prototype#406)
   ============================================================ *)

(* The canonical ticket template, as bytes, one of whose bytes may be changed to `~` (mutate: its place, or ~1), as
   a file of the folder .github/ISSUE_TEMPLATE/ of the planted repository *)
fn _issue_template {dir_len,name_len,file_len:nat | dir_len < 200; name_len < 100; file_len < 300}
  (dir: string dir_len, name: string name_len, file: string file_len, mutate: int): void = let
  var template : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant("templates/ISSUE_TEMPLATE/ticket.md", template)
  val @(template_array, template_len) = $B.to_arr(template)
  val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = _fill_loop(template_view, template_len, 0, text, "", "", "", mutate)
  val () = $A.drop<byte>(template_frozen, template_view)
  val () = $A.free<byte>($A.thaw<byte>(template_frozen))
in _put_rope(dir, name, ".github/ISSUE_TEMPLATE/", file, text) end

(* A repository with a canonical check.yml and the issue-template file ticket.md, equal to the canonical one except for the byte at mutate *)
fn _plant_with_issue_template {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len, mutate: int): void = let
  val () = _plant(dir, name)
  val () = _fill(dir, name, "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _issue_template(dir, name, "ticket.md", mutate)
in _commit(dir, name) end

(* An issue-template file equal to the canonical one passes *)
fn test_issue_template_equal_passes (): bool = let
  val dir = "build/pin-audit-tests/issue-equal"
  val () = _fresh(dir)
  val () = _plant_with_issue_template(dir, "tidy", ~1)
  val () = _names(dir, "tidy\n")
in _judge(dir, 0, ".github/ISSUE_TEMPLATE/ticket.md: pass, equal to the template ticket.md with its holes filled", "1 repositories, 2 workflow files: 0 passed by an allowlisted hash, 2 passed by a template, 0 not canonical", "templates: 6 read, 0 failing", "::error") end

(* ... and the same file with one byte changed fails, named *)
fn test_issue_template_one_byte_changed_fails (): bool = let
  val dir = "build/pin-audit-tests/issue-changed"
  val () = _fresh(dir)
  val () = _plant_with_issue_template(dir, "drift", 100)
  val () = _names(dir, "drift\n")
in _judge(dir, 1, "::error title=pin audit::drift: .github/ISSUE_TEMPLATE/ticket.md: not canonical: its sha256 ", "is not listed for it in tools/pin-audit/allowlist.txt and it equals no template with its holes filled", "== failing repositories: drift", "ISSUE_TEMPLATE/ticket.md: pass") end

(* A file that is not the canonical one's name is judged by its bytes too: another name with the canonical bytes passes, another text fails *)
fn test_issue_template_other_text_fails (): bool = let
  val dir = "build/pin-audit-tests/issue-other"
  val () = _fresh(dir)
  val () = _plant(dir, "own")
  val () = _fill(dir, "own", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _put(dir, "own", ".github/ISSUE_TEMPLATE/", "bug.md", "---\nname: Bug\n---\n")
  val () = _commit(dir, "own")
  val () = _names(dir, "own\n")
in _judge(dir, 1, "own: .github/ISSUE_TEMPLATE/bug.md: not canonical", "1 not canonical", "", "bug.md: pass") end

(* A file listed by hash with a ticket comment passes *)
fn test_issue_template_listed_with_ticket_passes (): bool = let
  val dir = "build/pin-audit-tests/issue-listed"
  val () = _fresh(dir)
  val () = _plant(dir, "own")
  val () = _fill(dir, "own", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _put(dir, "own", ".github/ISSUE_TEMPLATE/", "bug.md", "---\nname: Bug\n---\n")
  val () = _commit(dir, "own")
  val () = _names(dir, "own\n")
  val () = _allow(dir, "own/.github/ISSUE_TEMPLATE/bug.md", "---\nname: Bug\n---\n", "", "own#1")
in _judge(dir, 0, ".github/ISSUE_TEMPLATE/bug.md: pass, its sha256 is the current hash of tools/pin-audit/allowlist.txt line 1", "1 passed by an allowlisted hash", "", "::error") end

(* ... and the same listing without a ticket comment fails: the entry is a failure of the allowlist and lists nothing *)
fn test_issue_template_listed_without_ticket_fails (): bool = let
  val dir = "build/pin-audit-tests/issue-listed-no-ticket"
  val () = _fresh(dir)
  val () = _plant(dir, "own")
  val () = _fill(dir, "own", "check.yml", "templates/check.yml", "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", "17", ~1)
  val () = _put(dir, "own", ".github/ISSUE_TEMPLATE/", "bug.md", "---\nname: Bug\n---\n")
  val () = _commit(dir, "own")
  val () = _names(dir, "own\n")
  val () = _allow(dir, "own/.github/ISSUE_TEMPLATE/bug.md", "---\nname: Bug\n---\n", "", "")
in _judge(dir, 1, "::error title=pin audit::allowlist.txt line 1: it has no ticket comment", "own: .github/ISSUE_TEMPLATE/bug.md: not canonical", "1 entries, 1 failing", "bug.md: pass") end

(* The ticket of a repository whose issue template drifted shows the canonical one *)
fn test_issue_template_ticket_shows_canonical (): bool = let
  val dir = "build/pin-audit-tests/issue-ticket"
  val () = _fresh(dir)
  val () = _plant_with_issue_template(dir, "drift", 100)
  val judged = _judge_run(dir, _only_with_tickets("drift"), "GH_TOKEN=test-token", 1, "ticket created", "1 not canonical", "", "ticket updated")
  var canonical : $B.builder(0) = $B.create()
  val @(_, _) = read_constant("templates/ISSUE_TEMPLATE/ticket.md", canonical)
  val @(canonical_array, canonical_len) = $B.to_arr(canonical)
  val @(canonical_frozen, canonical_view) = $A.freeze<byte>(canonical_array)
  var expected : $B.sized_rope = $B.sized_rope_create()
  val () = _expect_start(expected)
  val () = $B.sized_rope_bput(expected, "## `.github/ISSUE_TEMPLATE/ticket.md`\n\nThe audit compares bytes: the file is exactly this text.\n\n```\n")
  val () = $B.sized_rope_copy(expected, canonical_view, 0, canonical_len)
  val () = $B.sized_rope_bput(expected, "```\n\n")
  val () = $A.drop<byte>(canonical_frozen, canonical_view)
  val () = $A.free<byte>($A.thaw<byte>(canonical_frozen))
  val () = _expect_end(expected, "drift")
  val body = _body_is(dir, "drift", expected)
in judged && body end

end
