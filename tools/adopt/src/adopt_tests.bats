(* adopt_tests -- the tests of adopt (bats-lang/repository-prototype#607), run by
   `bats test` in tools/adopt after `bats build`.

   Each case plants repositories with `git init` under
   build/adopt-tests/<case>/planted/<name>.git, a copy of the templates and a
   stand-in `gh` (the package's own gh_stand_in binary, copied as bin/gh), and
   runs the built dist/debug/adopt there with GIT_CONFIG_GLOBAL mapping
   https://github.com/bats-lang/ to the planted directory (url.<dir>.insteadOf)
   and PATH starting at the stand-in's directory. The program's output, its
   exit status, the files it writes and the calls it makes to gh are what is
   judged. The text a file must have is made here by the test's own fill of the
   template, so adopt's is compared with a text that is not its code. The case
   with pin_audit runs the built tools/pin-audit/dist/debug/pin_audit on the
   branch adopt pushed. A case's directory is kept (`bats clean` removes build/),
   and a failing case prints what it saw. Keyword: adopt tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use list as L
#use process as P
#use result as R

staload "support.sats"

(* ============================================================
   A case's directory
   ============================================================ *)

(* gitconfig of the case: https://github.com/bats-lang/ is the directory of its planted repositories
   (url.<dir>.insteadOf), and the identity adopt commits with *)
fn _config {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val cwd = $A.alloc<byte>(4096)
  val cwd_len = cwd_length(cwd)
  val @(cwd_frozen, cwd_view) = $A.freeze<byte>(cwd)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, "[url \"file://")
  val () = $B.sized_rope_copy(text, cwd_view, 0, cwd_len)
  val () = $B.sized_rope_bput(text, "/")
  val () = $B.sized_rope_bput(text, dir)
  val () = $B.sized_rope_bput(text, "/planted/\"]\n\tinsteadOf = https://github.com/bats-lang/\n[user]\n\tname = adopt-test\n\temail = adopt-test@example.com\n[commit]\n\tgpgsign = false\n")
  val _ = write_rope(join_path3(dir, "/", "gitconfig"), text)
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in () end

(* A text of the case's directory, as written *)
fn _write_text {dir_len,file_len,content_len:nat | dir_len < 200; file_len < 200; content_len < 100000}
  (dir: string dir_len, file: string file_len, content: string content_len): void = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = write_rope(join_path3(dir, "/", file), text)
in () end

(* A fresh dir: the templates, the stand-in gh, the gitconfig and the files the pin audit reads. The old one, if any, is removed first. *)
fn _fresh {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val _ = run_program("rm", args3(arg_text("-rf"), arg_text("--"), arg_text(dir)))
  val _ = run_program("mkdir", $L.list_vt_cons(arg_text("-p"), $L.list_vt_cons(arg_text("--"),
            args3(join_text2(dir, "/tools/pin-audit"), join_text2(dir, "/planted"), join_text2(dir, "/bin")))))
  val _ = run_program("cp", args3(arg_text("-R"), arg_text("../pin-audit/templates"), join_text2(dir, "/tools/pin-audit/templates")))
  val _ = run_program("cp", args2(arg_text("dist/debug/gh_stand_in"), join_text2(dir, "/bin/gh")))
  val () = _write_text(dir, "tools/pin-audit/allowlist.txt", "# no entries\n")
  val () = _write_text(dir, "tools/pin-audit/skipped.txt", "# no entries\n")
  val () = _write_text(dir, "tools/pin-audit/required.txt", "# no entries\n")
in _config(dir) end

(* dir/planted/name.git *)
fn _repo_arg {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/planted/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, ".git")
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* The path of a file of the planted repository dir/planted/name.git *)
fn _repo_path {dir_len,name_len,file_len:nat | dir_len < 200; name_len < 100; file_len < 300}
  (dir: string dir_len, name: string name_len, file: string file_len): path_text = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/planted/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, ".git/")
  val () = $B.bput(out, file)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* git in the planted repository, with a fixed identity *)
fn _git {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len, rest: $L.listv($P.arg_entry)): int =
  run_program("git", $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_repo_arg(dir, name),
    $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.name=plant"),
    $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.email=plant@example.com"),
    $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("commit.gpgsign=false"), rest)))))))))

(* A new repository dir/planted/name.git with one empty commit *)
fn _plant {dir_len,name_len:nat | dir_len < 200; name_len < 100} (dir: string dir_len, name: string name_len): void = let
  val _ = run_program("git", args3(arg_text("init"), arg_text("-q"), _repo_arg(dir, name)))
  val _ = _git(dir, name, $L.list_vt_cons(arg_text("commit"), args4(arg_text("-q"), arg_text("--allow-empty"), arg_text("-m"), arg_text("plant"))))
in () end

(* ============================================================
   The text a file must have
   ============================================================ *)

fun _fill_loop {l:agz}{template_len:nat | template_len <= 524288}{template_at:nat | template_at <= template_len}{commit_len,comment_len:nat} .<template_len - template_at>.
  (template_text: !$A.borrow(byte, l, 524288), template_len: int template_len, template_at: int template_at, out: !$B.sized_rope,
   commit: string commit_len, comment: string comment_len, mutate: int): void =
  if template_at >= template_len then ()
  else let
    val commit_end = lit_step(template_text, template_len, template_at, "@@COMMIT@@")
  in
    if commit_end >= 0 then let
      val () = $B.sized_rope_bput(out, commit)
    in _fill_loop(template_text, template_len, commit_end, out, commit, comment, mutate) end
    else let
      val comment_end = lit_step(template_text, template_len, template_at, "@@COMMENT@@")
    in
      if comment_end >= 0 then let
        val () = $B.sized_rope_bput(out, comment)
      in _fill_loop(template_text, template_len, comment_end, out, commit, comment, mutate) end
      else let
        val byte_value = byte2int0($A.read<byte>(template_text, template_at))
        val () = $B.sized_rope_put(out, $AR.low_byte(if template_at = mutate then 126 else byte_value))
      in _fill_loop(template_text, template_len, template_at + 1, out, commit, comment, mutate) end
    end
  end

(* The template of tools/pin-audit/templates with @@COMMIT@@ and @@COMMENT@@ filled with the case's values (mutate: the place
   of one byte of the template changed to `~`, or ~1), written to the path *)
fn _expect_to {name_len:nat | name_len < 100} (path: path_text, template: string name_len, mutate: int): void = let
  var template_text : $B.builder(0) = $B.create()
  val @(template_array, template_len) = join_path3("../pin-audit/templates/", "", template)
  val @(template_path_frozen, template_path_view) = $A.freeze<byte>(template_array)
  val @(ended, _) = read_file(template_path_view, template_len, template_text)
  val () = $A.drop<byte>(template_path_frozen, template_path_view)
  val () = $A.free<byte>($A.thaw<byte>(template_path_frozen))
  val @(text_array, text_len) = $B.to_arr(template_text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = _fill_loop(text_view, text_len, 0, text, "0123456789abcdef0123456789abcdef01234567", "repository-prototype main 0123456", mutate)
  val _ = write_rope(path, text)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in (case+ ended of | Read_whole() => () | Read_too_long() => () | Read_failed() => println! ("the template ", template, " could not be read")) end

(* The file the case expects of the template, dir/file *)
fn _expect {dir_len,file_len,name_len:nat | dir_len < 200; file_len < 200; name_len < 100} (dir: string dir_len, file: string file_len, template: string name_len): void =
  _expect_to(join_path3(dir, "/", file), template, ~1)

(* The file of the planted repository, made (with its folder) and committed: the template filled, with one byte changed (mutate) *)
fn _plant_file {dir_len,name_len,folder_len,template_len:nat | dir_len < 200; name_len < 100; folder_len < 100; template_len < 100}
  (dir: string dir_len, name: string name_len, folder: string folder_len, template: string template_len, mutate: int): void = let
  var folder_path : $B.builder(0) = $B.create()
  val () = $B.bput(folder_path, dir)
  val () = $B.bput(folder_path, "/planted/")
  val () = $B.bput(folder_path, name)
  val () = $B.bput(folder_path, ".git/")
  val () = $B.bput(folder_path, folder)
  val @(folder_array, folder_len2) = $B.to_arr(folder_path)
  val _ = run_program("mkdir", args3(arg_text("-p"), arg_text("--"), @(folder_array, folder_len2)))
  var file_path : $B.builder(0) = $B.create()
  val () = $B.bput(file_path, dir)
  val () = $B.bput(file_path, "/planted/")
  val () = $B.bput(file_path, name)
  val () = $B.bput(file_path, ".git/")
  val () = $B.bput(file_path, folder)
  val () = $B.bput(file_path, template)
  val @(file_array, file_len) = $B.to_arr(file_path)
  val () = _expect_to(@(file_array, file_len), template, mutate)
  val _ = _git(dir, name, args2(arg_text("add"), arg_text("-A")))
  val _ = _git(dir, name, $L.list_vt_cons(arg_text("commit"), args4(arg_text("-q"), arg_text("-m"), arg_text("plant file"), arg_text("--allow-empty"))))
in () end

(* ============================================================
   Running adopt
   ============================================================ *)

(* program (a path from the case's directory) in dir with the options, with the stand-in gh first on PATH and the planted
   repositories behind GIT_CONFIG_GLOBAL: its exit status, its output in out *)
fn _run_in {dir_len,program_len:nat | dir_len < 200; program_len < 200}
  (dir: string dir_len, program: string program_len, options: $L.listv($P.arg_entry), out: !$B.builder(0) >> $B.builder_v): @(int, read_end) = let
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
      $L.list_vt_cons(arg_text(program), options)))),
    args2(@(path_entry_array, path_entry_len), @(config_entry_array, config_entry_len)), out)
  val () = $A.drop<byte>(old_frozen, old_view)
  val () = $A.free<byte>($A.thaw<byte>(old_frozen))
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in result end

(* The arguments after the options: the template, the commit and the comment of the case, then the entries *)
fn _standard {template_len:nat | template_len < 100} (template: string template_len, entries: $L.listv($P.arg_entry)): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text(template), $L.list_vt_cons(arg_text("0123456789abcdef0123456789abcdef01234567"),
  $L.list_vt_cons(arg_text("repository-prototype main 0123456"), entries)))

(* Runs adopt with the options and judges it: the exit status is want, the output holds the three texts and lacks the last. A failing case prints what it saw. *)
fn _judge {dir_len,first_len,second_len,third_len,absent_len:nat | dir_len < 200}
  (dir: string dir_len, options: $L.listv($P.arg_entry), want: int, first: string first_len, second: string second_len, third: string third_len, absent: string absent_len): bool = let
  var out : $B.builder(0) = $B.create()
  val @(status, ended) = _run_in(dir, "../../../dist/debug/adopt", options, out)
  val @(output_array, output_len) = $B.to_arr(out)
  val @(output_frozen, output_view) = $A.freeze<byte>(output_array)
  val whole = (case+ ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
  val good = whole && status = want && output_has(output_view, output_len, first) && output_has(output_view, output_len, second) && output_has(output_view, output_len, third) && output_lacks(output_view, output_len, absent): bool
  val () =
    if good then ()
    else let
      val () = println! ("FAIL ", dir, ": exit status ", status, " (wanted ", want, "), the output was read whole: ", whole)
      val () = println! ("  wanted: ", first, " | ", second, " | ", third, " | and lacking: ", absent)
      val () = println! ("  adopt's output:")
      val () = print_range(output_view, 0, output_len)
    in println! ("  (the case's directory ", dir, " is kept)") end
  val () = $A.drop<byte>(output_frozen, output_view)
  val () = $A.free<byte>($A.thaw<byte>(output_frozen))
in good end

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

(* Whether the file of the case's directory begins with the text *)
fn _file_begins {dir_len,file_len,start_len:nat | dir_len < 200; file_len < 200; start_len > 0}
  (dir: string dir_len, file: string file_len, start: string start_len): bool = let
  var text : $B.builder(0) = $B.create()
  val @(_, _) = _read_file_of(dir, file, text)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val good = lit_step(text_view, text_len, 0, start) >= 0
  val () = if good then () else println! ("FAIL ", dir, "/", file, ": it does not begin with: ", start)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in good end

(* Whether the file of the case's directory ends with the text, and holds it once *)
fn _file_ends {dir_len,file_len,end_len:nat | dir_len < 200; file_len < 200; end_len > 0}
  (dir: string dir_len, file: string file_len, last: string end_len): bool = let
  var text : $B.builder(0) = $B.create()
  val @(_, _) = _read_file_of(dir, file, text)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val last_len = text_length(last)
  val good = (if text_len >= last_len then lit_step(text_view, text_len, text_len - last_len, last) >= 0 else false): bool
  val () = if good then () else println! ("FAIL ", dir, "/", file, ": it does not end with: ", last)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in good end

(* Whether the file dir/planted/name.git/rel is the file dir/expected *)
fn _planted_is {dir_len,name_len,rel_len,expected_len:nat | dir_len < 100; name_len < 100; rel_len < 200; expected_len < 100}
  (dir: string dir_len, name: string name_len, rel: string rel_len, expected: string expected_len): bool = let
  var actual : $B.builder(0) = $B.create()
  val () = $B.bput(actual, dir)
  val () = $B.bput(actual, "/planted/")
  val () = $B.bput(actual, name)
  val () = $B.bput(actual, ".git/")
  val () = $B.bput(actual, rel)
  val @(actual_array, actual_len) = $B.to_arr(actual)
  val same = run_program("cmp", args3(arg_text("-s"), join_text2(dir, expected), @(actual_array, actual_len))) = 0
  val () = if same then () else println! ("FAIL ", dir, ": ", rel, " of ", name, " is not ", expected)
in same end

(* The branch of a planted repository checked out *)
fn _checkout {dir_len,name_len,branch_len:nat | dir_len < 200; name_len < 100; branch_len < 100}
  (dir: string dir_len, name: string name_len, branch: string branch_len): bool =
  _git(dir, name, $L.list_vt_cons(arg_text("checkout"), args2(arg_text("-q"), arg_text(branch)))) = 0

(* The branch of a planted repository exists *)
fn _has_branch {dir_len,name_len,branch_len:nat | dir_len < 200; name_len < 100; branch_len < 100}
  (dir: string dir_len, name: string name_len, branch: string branch_len): bool =
  _git(dir, name, $L.list_vt_cons(arg_text("show-ref"), args3(arg_text("--quiet"), arg_text("--verify"), join_text2("refs/heads/", branch)))) = 0

(* Writes `Head: <the head of the branch>` and a newline to the file of the case, and whether the body contains that line whole *)
fn _body_has_head {dir_len,name_len,branch_len,body_len:nat | dir_len < 100; name_len < 100; branch_len < 100; body_len < 100}
  (dir: string dir_len, name: string name_len, branch: string branch_len, body: string body_len): bool = let
  var head : $B.builder(0) = $B.create()
  val @(status, _) = capture_with("git",
    $L.list_vt_cons(arg_text("git"), $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_repo_arg(dir, name), args2(arg_text("rev-parse"), arg_text(branch))))),
    no_arguments(), head)
  val @(head_array, head_len) = $B.to_arr(head)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  var line : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(line, "Head: ")
  val () = if head_len >= 40 then $B.sized_rope_copy(line, head_view, 0, 40) else ()
  val () = $B.sized_rope_bput(line, "\n")
  val _ = write_rope(join_path3(dir, "/", "head-line.txt"), line)
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  val found = (status = 0 && head_len >= 40
    && run_program("grep", $L.list_vt_cons(arg_text("-q"), $L.list_vt_cons(arg_text("-x"), $L.list_vt_cons(arg_text("-F"),
         args4(arg_text("-f"), join_text2(dir, "/head-line.txt"), arg_text("--"), join_text2(dir, body)))))) = 0): bool
  val () = if found then () else println! ("FAIL ", dir, ": the body has no line Head: <the head of ", branch, ">")
in found end

(* Whether the file body of the case's directory has the line, whole (a file of its own is written for grep -x -F -f) *)
fn _has_line {dir_len,body_len,line_len:nat | dir_len < 100; body_len < 100; line_len < 4000}
  (dir: string dir_len, body: string body_len, line: string line_len): bool = let
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, line)
  val () = $B.sized_rope_bput(text, "\n")
  val _ = write_rope(join_path3(dir, "/", "line.txt"), text)
  val found = run_program("grep", $L.list_vt_cons(arg_text("-q"), $L.list_vt_cons(arg_text("-x"), $L.list_vt_cons(arg_text("-F"),
    args4(arg_text("-f"), join_text2(dir, "/line.txt"), arg_text("--"), join_text2(dir, body)))))) = 0
  val () = if found then () else println! ("FAIL ", dir, ": the body has no line: ", line)
in found end

$UNITTEST.run begin

(* A repository without the file gets a draft pull request: the file written, the branch pushed with it, gh called with the title and the body *)
fn test_adopts_a_repository (): bool = let
  val dir = "build/adopt-tests/adopt"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _expect(dir, "expected.yml", "canonical-files.yml")
  val ran = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  val pushed = _checkout(dir, "alpha", "adopt-7")
  val written = _planted_is(dir, "alpha", ".github/workflows/canonical-files.yml", "/expected.yml")
  val called = _file_judge(dir, "gh-calls.txt",
    "pr create -R bats-lang/alpha --draft --head adopt-7 --title Adopt canonical-files.yml at repository-prototype 0123456789abcdef0123456789abcdef01234567 --body-file adopt-clones/alpha.body.md\n", "")
in ran && pushed && written && called end

(* The file the pin audit passes: the audit of the organisation's repositories accepts the branch adopt pushed *)
fn test_pin_audit_accepts_the_file (): bool = let
  val dir = "build/adopt-tests/audit"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val ran = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  val pushed = _checkout(dir, "alpha", "adopt-7")
  var out : $B.builder(0) = $B.create()
  val @(status, _) = _run_in(dir, "../../../../pin-audit/dist/debug/pin_audit", args2(arg_text("--repository"), arg_text("alpha")), out)
  val @(output_array, output_len) = $B.to_arr(out)
  val @(output_frozen, output_view) = $A.freeze<byte>(output_array)
  val accepted = status = 0 && output_has(output_view, output_len, "canonical-files.yml: pass, equal to the template canonical-files.yml with its holes filled")
  val () =
    if accepted then ()
    else let
      val () = println! ("FAIL ", dir, ": pin_audit --repository alpha exited ", status, ", its output:")
    in print_range(output_view, 0, output_len) end
  val () = $A.drop<byte>(output_frozen, output_view)
  val () = $A.free<byte>($A.thaw<byte>(output_frozen))
in ran && pushed && accepted end

(* The body: its first line, Plan, Execution, Evidence with the commands adopt ran, the Head line of the pushed commit, and the footer as its last line *)
fn test_body_lines (): bool = let
  val dir = "build/adopt-tests/body"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val ran = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  val first = _file_begins(dir, "adopt-clones/alpha.body.md", "Fixes bats-lang/alpha#7\n")
  val plan = _file_judge(dir, "adopt-clones/alpha.body.md", "\n## Plan\n\nDone when: the file `.github/workflows/canonical-files.yml` is `tools/pin-audit/templates/canonical-files.yml` of bats-lang/repository-prototype at `0123456789abcdef0123456789abcdef01234567` with its holes filled.\n\n1. `git show --stat --format= HEAD`", "")
  val execution = _file_judge(dir, "adopt-clones/alpha.body.md", "\n## Execution\n\n`adopt` cloned bats-lang/alpha, filled `@@COMMIT@@` with `0123456789abcdef0123456789abcdef01234567` and `@@COMMENT@@` with `repository-prototype main 0123456`", "")
  val evidence = _file_judge(dir, "adopt-clones/alpha.body.md", "\n## Evidence\n\n```\n$ git rev-parse HEAD\n", "")
  val stat = _file_judge(dir, "adopt-clones/alpha.body.md", "$ git show --stat --format= HEAD\n .github/workflows/canonical-files.yml | ", "")
  val head = _body_has_head(dir, "alpha", "adopt-7", "/adopt-clones/alpha.body.md")
  val footer = _file_ends(dir, "adopt-clones/alpha.body.md", " Generated with [Claude Code](https://claude.com/claude-code)\n")
  val footer_line = _has_line(dir, "/adopt-clones/alpha.body.md", "🤖 Generated with [Claude Code](https://claude.com/claude-code)")
  val head_line = _file_judge(dir, "adopt-clones/alpha.body.md", "```\n\nHead: ", "")
in ran && first && plan && execution && evidence && stat && head && footer && footer_line && head_line end

(* The pull request body lint of the organisation (tools/text-lint, built before this test) finds nothing in the body for the pushed head *)
fn test_body_passes_the_body_lint (): bool = let
  val dir = "build/adopt-tests/lint"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val ran = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  var head : $B.builder(0) = $B.create()
  val @(head_status, _) = capture_with("git",
    $L.list_vt_cons(arg_text("git"), $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_repo_arg(dir, "alpha"), args2(arg_text("rev-parse"), arg_text("adopt-7"))))),
    no_arguments(), head)
  val @(head_array, head_len) = $B.to_arr(head)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  val head_ok = head_status = 0 && head_len >= 40
  var out : $B.builder(0) = $B.create()
  val @(lint_status, _) =
    _run_in(dir, "../../../../text-lint/dist/debug/text_lint",
      $L.list_vt_cons(arg_text("body"), $L.list_vt_cons(arg_text("adopt-clones/alpha.body.md"),
      args2(arg_range("", head_view, 0, 40, ""), arg_text("../../../../text-lint/phrases.txt")))), out)
  val @(out_array, out_len) = $B.to_arr(out)
  val @(out_frozen, out_view) = $A.freeze<byte>(out_array)
  val clean = head_ok && lint_status = 0 && output_has(out_view, out_len, "ok\n")
  val () =
    if clean then ()
    else let
      val () = println! ("FAIL ", dir, ": text_lint body exited ", lint_status, ", its output:")
    in print_range(out_view, 0, out_len) end
  val () = $A.drop<byte>(out_frozen, out_view)
  val () = $A.free<byte>($A.thaw<byte>(out_frozen))
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
in ran && clean end

(* A second run: the branch is already pushed, so the repository is left alone and gh is not called again *)
fn test_second_run_is_a_noop (): bool = let
  val dir = "build/adopt-tests/second"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val first = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  val _ = run_program("rm", args3(arg_text("-f"), arg_text("--"), join_text2(dir, "/gh-calls.txt")))
  val second = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0, "alpha: - - no-op: the branch is already pushed", "", "", "draft")
  val quiet = _file_judge(dir, "gh-calls.txt", "", "pr create")
in first && second && quiet end

(* A repository that has the file as the template gives it: a no-op that says so, nothing pushed, gh not called *)
fn test_existing_file_is_a_noop (): bool = let
  val dir = "build/adopt-tests/existing"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _plant_file(dir, "alpha", ".github/workflows/", "canonical-files.yml", ~1)
  val ran = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 0,
    "alpha: - - no-op: .github/workflows/canonical-files.yml is already the template with its holes filled", "", "", "draft")
  val quiet = _file_judge(dir, "gh-calls.txt", "", "pr create")
  val unpushed = ~_has_branch(dir, "alpha", "adopt-7")
in ran && quiet && unpushed end

(* A file that differs by one byte is refused, the byte named (the first and a later one); the others are still done *)
fn test_one_byte_difference_is_refused (): bool = let
  val dir = "build/adopt-tests/byte"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _plant(dir, "beta")
  val () = _plant_file(dir, "beta", ".github/workflows/", "canonical-files.yml", 0)
  val () = _plant(dir, "gamma")
  val () = _plant_file(dir, "gamma", ".github/workflows/", "canonical-files.yml", 5)
  val ran = _judge(dir, _standard("canonical-files.yml", args3(arg_text("alpha#7"), arg_text("beta#8"), arg_text("gamma#9"))), 1,
    "beta: - - refused: .github/workflows/canonical-files.yml differs from the template with its holes filled at byte 1\n",
    "gamma: - - refused: .github/workflows/canonical-files.yml differs from the template with its holes filled at byte 6\n",
    "alpha: https://example.invalid/pull/1 ", "beta: https://")
  val calls = _file_judge(dir, "gh-calls.txt", "-R bats-lang/alpha ", "bats-lang/beta")
  val unpushed = ~_has_branch(dir, "beta", "adopt-8") && ~_has_branch(dir, "gamma", "adopt-9")
in ran && calls && unpushed end

(* --only does the one repository of the list and prints exactly what it wrote *)
fn test_only_prints_the_file (): bool = let
  val dir = "build/adopt-tests/only"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _plant(dir, "beta")
  val ran = _judge(dir, $L.list_vt_cons(arg_text("--only"), $L.list_vt_cons(arg_text("beta"), _standard("canonical-files.yml", args2(arg_text("alpha#7"), arg_text("beta#8"))))), 0,
    "beta: wrote .github/workflows/canonical-files.yml:\n# A pull request that changes a workflow",
    "    uses: bats-lang/repository-prototype/.github/workflows/canonical-files-check.yml@0123456789abcdef0123456789abcdef01234567 # repository-prototype main 0123456\n",
    "beta: https://example.invalid/pull/1 ", "alpha:")
  val calls = _file_judge(dir, "gh-calls.txt", "-R bats-lang/beta --draft --head adopt-8 ", "bats-lang/alpha")
  val only = _has_branch(dir, "beta", "adopt-8") && ~_has_branch(dir, "alpha", "adopt-7")
in ran && calls && only end

(* An issue template goes to .github/ISSUE_TEMPLATE, byte for byte (it has no holes) *)
fn test_issue_template (): bool = let
  val dir = "build/adopt-tests/issue"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _expect(dir, "expected-ticket.md", "ISSUE_TEMPLATE/ticket.md")
  val ran = _judge(dir, _standard("ISSUE_TEMPLATE/ticket.md", args1(arg_text("alpha#7"))), 0, "alpha: https://example.invalid/pull/1 ", " draft", "", "failed")
  val pushed = _checkout(dir, "alpha", "adopt-7")
  val written = _planted_is(dir, "alpha", ".github/ISSUE_TEMPLATE/ticket.md", "/expected-ticket.md")
  val body = _file_judge(dir, "adopt-clones/alpha.body.md", "Done when: the file `.github/ISSUE_TEMPLATE/ticket.md` is `tools/pin-audit/templates/ISSUE_TEMPLATE/ticket.md`", "")
in ran && pushed && written && body end

(* A template with a @@MINUTE@@ hole is refused: the minute is not adopt's to choose *)
fn test_minute_hole_is_refused (): bool = let
  val dir = "build/adopt-tests/minute"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val ran = _judge(dir, _standard("relock.yml", args1(arg_text("alpha#7"))), 1,
    "alpha: - - refused: the template has a @@MINUTE@@ hole, which adopt does not fill", "", "", "draft")
  val quiet = _file_judge(dir, "gh-calls.txt", "", "pr create")
  val unpushed = ~_has_branch(dir, "alpha", "adopt-7")
in ran && quiet && unpushed end

(* A gh that fails is a failure of the repository, said with its step *)
fn test_gh_failure_is_reported (): bool = let
  val dir = "build/adopt-tests/gh-fails"
  val () = _fresh(dir)
  val () = _plant(dir, "alpha")
  val () = _write_text(dir, "gh-fail", "")
in _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7"))), 1, "alpha: - - failed: gh pr create (status 1)", "", "", "draft") end

(* A repository that cannot be cloned is a failure of the repository, said with its step *)
fn test_missing_repository_fails (): bool = let
  val dir = "build/adopt-tests/missing"
  val () = _fresh(dir)
in _judge(dir, _standard("canonical-files.yml", args1(arg_text("absent#7"))), 1, "absent: - - failed: git clone (status 128)", "", "", "draft") end

(* Arguments adopt does not take: status 2 and the usage, nothing cloned *)
fn test_arguments_are_refused (): bool = let
  val dir = "build/adopt-tests/arguments"
  val () = _fresh(dir)
  val none = _judge(dir, _standard("canonical-files.yml", no_arguments()), 2, "usage: adopt [--only NAME] TEMPLATE COMMIT COMMENT NAME#TICKET...", "", "", "failed")
  val short_commit = _judge(dir, $L.list_vt_cons(arg_text("canonical-files.yml"), $L.list_vt_cons(arg_text("0123456789abcdef0123456789abcdef0123456"),
    $L.list_vt_cons(arg_text("repository-prototype main 0123456"), args1(arg_text("alpha#7"))))), 2, "usage: adopt", "", "", "failed")
  val upper_commit = _judge(dir, $L.list_vt_cons(arg_text("canonical-files.yml"), $L.list_vt_cons(arg_text("0123456789ABCDEF0123456789abcdef01234567"),
    $L.list_vt_cons(arg_text("repository-prototype main 0123456"), args1(arg_text("alpha#7"))))), 2, "usage: adopt", "", "", "failed")
  val empty_comment = _judge(dir, $L.list_vt_cons(arg_text("canonical-files.yml"), $L.list_vt_cons(arg_text("0123456789abcdef0123456789abcdef01234567"),
    $L.list_vt_cons(arg_text(""), args1(arg_text("alpha#7"))))), 2, "usage: adopt", "", "", "failed")
  val no_ticket = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha"))), 2, "usage: adopt", "", "", "failed")
  val empty_ticket = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#"))), 2, "usage: adopt", "", "", "failed")
  val letter_ticket = _judge(dir, _standard("canonical-files.yml", args1(arg_text("alpha#7x"))), 2, "usage: adopt", "", "", "failed")
  val slash_name = _judge(dir, _standard("canonical-files.yml", args1(arg_text("a/b#7"))), 2, "usage: adopt", "", "", "failed")
  val path_template = _judge(dir, _standard("../x.yml", args1(arg_text("alpha#7"))), 2, "usage: adopt", "", "", "failed")
  val unlisted = _judge(dir, $L.list_vt_cons(arg_text("--only"), $L.list_vt_cons(arg_text("zeta"), _standard("canonical-files.yml", args1(arg_text("alpha#7"))))), 2, "usage: adopt", "", "", "failed")
  val only_alone = _judge(dir, args1(arg_text("--only")), 2, "usage: adopt", "", "", "failed")
in none && short_commit && upper_commit && empty_comment && no_ticket && empty_ticket && letter_ticket && slash_name && path_template && unlisted && only_alone end

end
