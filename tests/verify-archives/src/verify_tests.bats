(* verify_tests -- the tests of scripts/verify-archives.sh (bats-lang/
   repository-prototype#396), run by `bats test` in tests/verify-archives
   after `bats build`. Keyword: verify-archives tests.

   Each case plants a git repository under build/verify-tests/<case>/repo
   with `git init`: a base commit holding the archive pkg/old_1.bats (a real
   zip, made with `zip`, and its sidecar), then the change under test as a
   second commit. It runs the script there as `sh <script> HEAD~1`, with a
   stand-in `bats` first on PATH (the package's own bats_stand_in binary,
   copied as bin/bats; its rules are in its source). The script's exit
   status and output are what is judged; every case prints its output, so
   the run is its own evidence. The script is scripts/verify-archives.sh, or
   the file named by the environment variable VERIFY_ARCHIVES_SCRIPT. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use list as L
#use process as P
#use result as R

staload "support.sats"

(* ============================================================
   A case's repository
   ============================================================ *)

(* dir/repo/folder/name and the suffix, as a path *)
fn _archive_path {dir_len,folder_len,name_len,suffix_len:nat | dir_len < 200; folder_len < 100; name_len < 100; suffix_len < 100}
  (dir: string dir_len, folder: string folder_len, name: string name_len, suffix: string suffix_len): path_text = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, dir)
  val () = $B.bput(out, "/repo/")
  val () = $B.bput(out, folder)
  val () = $B.bput(out, "/")
  val () = $B.bput(out, name)
  val () = $B.bput(out, suffix)
  val @(array, length) = $B.to_arr(out)
in @(array, length) end

(* A fresh case: the stand-in bats, the fixture files of the archives, an
   empty repository. The old directory, if any, is removed first. *)
fn _fresh {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val _ = run_program("rm", args3(arg_text("-rf"), arg_text("--"), arg_text(dir)))
  val _ = run_program("mkdir", $L.list_vt_cons(arg_text("-p"), $L.list_vt_cons(arg_text("--"),
            args3(join_text2(dir, "/repo"), join_text2(dir, "/bin"), join_text2(dir, "/payload")))))
  val _ = run_program("cp", args2(arg_text("dist/debug/bats_stand_in"), join_text2(dir, "/bin/bats")))
  var package_file : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(package_file, "name = \"fixture\"\n")
  val _ = write_rope(join_path3(dir, "/payload/", "bats.toml"), package_file)
  var depends_file : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(depends_file, "the package depends on the repository\n")
  val _ = write_rope(join_path3(dir, "/payload/", "depends"), depends_file)
  val _ = run_program("git", args3(arg_text("init"), arg_text("-q"), join_text2(dir, "/repo")))
in () end

(* The folder dir/repo/folder made, if it was not *)
fn _folder {dir_len,folder_len:nat | dir_len < 200; folder_len < 100}
  (dir: string dir_len, folder: string folder_len): void = let
  val _ = run_program("mkdir", args3(arg_text("-p"), arg_text("--"), path_argument(join_path3(dir, "/repo/", folder))))
in () end

(* dir/repo/folder/name made a zip of the fixture files: bats.toml, and
   depends too when with_depends (the stand-in's check can then fail) *)
fn _zip {dir_len,folder_len,name_len:nat | dir_len < 200; folder_len < 100; name_len < 100}
  (dir: string dir_len, folder: string folder_len, name: string name_len, with_depends: bool): void = let
  val () = _folder(dir, folder)
  val _ = run_program("rm", args3(arg_text("-f"), arg_text("--"), path_argument(_archive_path(dir, folder, name, ""))))
  val _ =
    if with_depends then
      run_program("zip", $L.list_vt_cons(arg_text("-q"), $L.list_vt_cons(arg_text("-j"),
        args3(path_argument(_archive_path(dir, folder, name, "")), join_text2(dir, "/payload/bats.toml"), join_text2(dir, "/payload/depends")))))
    else
      run_program("zip", $L.list_vt_cons(arg_text("-q"), $L.list_vt_cons(arg_text("-j"),
        args2(path_argument(_archive_path(dir, folder, name, "")), join_text2(dir, "/payload/bats.toml")))))
in () end

(* The archive and its sidecar removed *)
fn _remove {dir_len,folder_len,name_len:nat | dir_len < 200; folder_len < 100; name_len < 100}
  (dir: string dir_len, folder: string folder_len, name: string name_len): void = let
  val _ = run_program("rm", args4(arg_text("-f"), arg_text("--"), path_argument(_archive_path(dir, folder, name, "")),
            path_argument(_archive_path(dir, folder, name, ".sha256"))))
in () end

(* The text as the file dir/repo/folder/name *)
fn _text {dir_len,folder_len,name_len,content_len:nat | dir_len < 200; folder_len < 100; name_len < 100; content_len < 1000}
  (dir: string dir_len, folder: string folder_len, name: string name_len, content: string content_len): void = let
  val () = _folder(dir, folder)
  var text : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(text, content)
  val _ = write_rope(_archive_path(dir, folder, name, ""), text)
in () end

(* The sidecar of the archive dir/repo/folder/name: the line sha256sum
   writes for it (the sha256 of the archive and its name) when matching, and
   the sha256 of nothing but zeros when not *)
fn _sidecar {dir_len,folder_len,name_len:nat | dir_len < 200; folder_len < 100; name_len < 100}
  (dir: string dir_len, folder: string folder_len, name: string name_len, matching: bool): void = let
  val @(path_array, path_len) = _archive_path(dir, folder, name, "")
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var archive : $B.builder(0) = $B.create()
  val @(_, _) = read_file(path_view, path_len, archive)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val @(archive_array, archive_len) = $B.to_arr(archive)
  val hash = sha256_hex(archive_array, archive_len)
  val () = $A.free<byte>(archive_array)
  val @(hash_frozen, hash_view) = $A.freeze<byte>(hash)
  var line : $B.sized_rope = $B.sized_rope_create()
  val () =
    if matching then $B.sized_rope_copy(line, hash_view, 0, 64)
    else $B.sized_rope_bput(line, "0000000000000000000000000000000000000000000000000000000000000000")
  val () = $B.sized_rope_bput(line, "  ")
  val () = $B.sized_rope_bput(line, name)
  val () = $B.sized_rope_bput(line, "\n")
  val () = $A.drop<byte>(hash_frozen, hash_view)
  val () = $A.free<byte>($A.thaw<byte>(hash_frozen))
  val _ = write_rope(_archive_path(dir, folder, name, ".sha256"), line)
in () end

(* Everything written so far as a commit of the case's repository *)
fn _commit {dir_len,message_len:nat | dir_len < 200; message_len < 100}
  (dir: string dir_len, message: string message_len): void = let
  val _ = run_program("git", args4(arg_text("-C"), join_text2(dir, "/repo"), arg_text("add"), arg_text("-A")))
  val _ = run_program("git", $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(join_text2(dir, "/repo"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.name=plant"),
            $L.list_vt_cons(arg_text("-c"), $L.list_vt_cons(arg_text("user.email=plant@example.com"),
            args4(arg_text("commit"), arg_text("-q"), arg_text("-m"), arg_text(message)))))))))
in () end

(* The base of every case: the published archive pkg/old_1.bats (it depends
   on the repository) with its sidecar *)
fn _base {dir_len:nat | dir_len < 200} (dir: string dir_len): void = let
  val () = _fresh(dir)
  val () = _zip(dir, "pkg", "old_1.bats", true)
  val () = _sidecar(dir, "pkg", "old_1.bats", true)
  val () = _commit(dir, "base")
in () end

(* ============================================================
   Running the script
   ============================================================ *)

(* The script named by the environment, as an argument *)
fn _override_argument {l:agz}{k:nat | k <= 8192} (view: !$A.borrow(byte, l, 8192), length: int k): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = put_range(view, 0, length, out)
  val @(array, kept) = $B.to_arr(out)
in @(array, kept) end

(* scripts/verify-archives.sh of this checkout (the current directory is
   tests/verify-archives), as an argument *)
fn _default_argument {l:agz}{k:nat | k <= 4096} (cwd_view: !$A.borrow(byte, l, 4096), cwd_len: int k): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = put_range(cwd_view, 0, cwd_len, out)
  val () = $B.bput(out, "/../../scripts/verify-archives.sh")
  val @(array, kept) = $B.to_arr(out)
in @(array, kept) end

(* The value of the environment variable, in a buffer of 8192 bytes: its length *)
fn _variable {name_len:nat | name_len < 100} {l:agz} (name: string name_len, buffer: !$A.arr(byte, l, 8192)): [k:nat | k <= 8192] int k = let
  var name_builder : $B.builder(0) = $B.create()
  val () = $B.bput(name_builder, name)
  val @(name_array, _) = $B.to_arr(name_builder)
  val length = (case+ $E.get_cstr(name_array, 524288, buffer, 8192) of | ~$R.some(k) => k | ~$R.none() => 0): [k:nat | k <= 8192] int k
  val () = $A.free<byte>(name_array)
in length end

(* The script on the case's repository with the stand-in bats first on PATH:
   its exit status, its output (standard output; the errors of the script
   are sent to it by `2>&1` in the call) in out *)
fn _script {dir_len:nat | dir_len < 200} (dir: string dir_len, out: !$B.builder(0) >> $B.builder_v): @(int, read_end) = let
  val cwd = $A.alloc<byte>(4096)
  val cwd_len = cwd_length(cwd)
  val @(cwd_frozen, cwd_view) = $A.freeze<byte>(cwd)
  val old_path = $A.alloc<byte>(8192)
  val old_path_len = _variable("PATH", old_path)
  val @(old_frozen, old_view) = $A.freeze<byte>(old_path)
  val override = $A.alloc<byte>(8192)
  val override_len = _variable("VERIFY_ARCHIVES_SCRIPT", override)
  val @(override_frozen, override_view) = $A.freeze<byte>(override)
  val script_argument =
    (if override_len > 0 then _override_argument(override_view, override_len)
     else _default_argument(cwd_view, cwd_len)): $P.arg_entry
  var path_entry : $B.builder(0) = $B.create()
  val () = $B.bput(path_entry, "PATH=")
  val () = put_range(cwd_view, 0, cwd_len, path_entry)
  val () = $B.bput(path_entry, "/")
  val () = $B.bput(path_entry, dir)
  val () = $B.bput(path_entry, "/bin:")
  val () = put_range(old_view, 0, old_path_len, path_entry)
  val @(path_entry_array, path_entry_len) = $B.to_arr(path_entry)
  val result = capture_with("env",
    $L.list_vt_cons(arg_text("env"), $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(join_text2(dir, "/repo"),
      $L.list_vt_cons(arg_text("sh"), args3(script_argument, arg_text("HEAD~1"), arg_text("--")))))),
    args1(@(path_entry_array, path_entry_len)), out)
  val () = $A.drop<byte>(override_frozen, override_view)
  val () = $A.free<byte>($A.thaw<byte>(override_frozen))
  val () = $A.drop<byte>(old_frozen, old_view)
  val () = $A.free<byte>($A.thaw<byte>(old_frozen))
  val () = $A.drop<byte>(cwd_frozen, cwd_view)
  val () = $A.free<byte>($A.thaw<byte>(cwd_frozen))
in result end

(* Runs the script on the case and judges it: the exit status is want, the
   output holds the three texts and lacks the last. The output is printed
   for every case; a failing case says what was wanted. *)
fn _judge {dir_len,first_len,second_len,third_len,absent_len:nat | dir_len < 200}
  (dir: string dir_len, want: int, first: string first_len, second: string second_len, third: string third_len, absent: string absent_len): bool = let
  var out : $B.builder(0) = $B.create()
  val @(status, ended) = _script(dir, out)
  val @(output_array, output_len) = $B.to_arr(out)
  val @(output_frozen, output_view) = $A.freeze<byte>(output_array)
  val whole = (case+ ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
  val good = whole && status = want && output_has(output_view, output_len, first) && output_has(output_view, output_len, second)
             && output_has(output_view, output_len, third) && output_lacks(output_view, output_len, absent): bool
  val () = println! ("== ", dir, ": exit status ", status, " (wanted ", want, "), output:")
  val () = print_range(output_view, 0, output_len)
  val () =
    if good then println! ("== ", dir, ": as wanted")
    else let
      val () = println! ("FAIL ", dir, ": the output was read whole: ", whole)
    in println! ("  wanted: ", first, " | ", second, " | ", third, " | and lacking: ", absent) end
  val () = $A.drop<byte>(output_frozen, output_view)
  val () = $A.free<byte>($A.thaw<byte>(output_frozen))
in good end

(* ============================================================
   Cases
   ============================================================ *)

$UNITTEST.run begin

(* A .bats source deep in the tree (five components, then four) is not an
   archive: nothing is checked and the change passes *)
fn test_deep_source_passes (): bool = let
  val dir = "build/verify-tests/deep-source"
  val () = _base(dir)
  val () = _text(dir, "tools/pin-audit/src/bin", "pin_audit.bats", "implement main0 () = ()\n")
  val () = _text(dir, "tools/pin-audit/src", "audit.bats", "implement main0 () = ()\n")
  val () = _commit(dir, "change")
in _judge(dir, 0, "no archives added", "", "", "FAIL") end

(* An archive added at the root without its sidecar fails *)
fn test_root_archive_without_sidecar_fails (): bool = let
  val dir = "build/verify-tests/root-no-sidecar"
  val () = _base(dir)
  val () = _zip(dir, ".", "new_2.bats", false)
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: new_2.bats has no sidecar", "", "", "ok   ") end

(* ... in a package's directory ... *)
fn test_package_archive_without_sidecar_fails (): bool = let
  val dir = "build/verify-tests/package-no-sidecar"
  val () = _base(dir)
  val () = _zip(dir, "pkg", "new_2.bats", false)
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: pkg/new_2.bats has no sidecar", "", "", "ok   ") end

(* ... and in a namespace's package directory (three components) *)
fn test_namespace_archive_without_sidecar_fails (): bool = let
  val dir = "build/verify-tests/namespace-no-sidecar"
  val () = _base(dir)
  val () = _zip(dir, "wasm.bats-packages.dev/bridge", "new_2.bats", false)
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: wasm.bats-packages.dev/bridge/new_2.bats has no sidecar", "", "", "ok   ") end

(* A sidecar that does not match its archive fails *)
fn test_mismatching_sidecar_fails (): bool = let
  val dir = "build/verify-tests/mismatching-sidecar"
  val () = _base(dir)
  val () = _zip(dir, "pkg", "new_2.bats", false)
  val () = _sidecar(dir, "pkg", "new_2.bats", false)
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: pkg/new_2.bats does not match its sidecar", "", "", "ok   ") end

(* An archive with a matching sidecar passes: its lock and check run (the
   stand-in), and so does the regression loop over the other packages *)
fn test_matching_sidecar_passes (): bool = let
  val dir = "build/verify-tests/matching-sidecar"
  val () = _base(dir)
  val () = _zip(dir, "pkg", "new_2.bats", false)
  val () = _sidecar(dir, "pkg", "new_2.bats", true)
  val () = _commit(dir, "change")
in _judge(dir, 0, "ok   pkg/new_2.bats", "", "", "FAIL") end

(* ... also in a namespace's package directory *)
fn test_namespace_matching_sidecar_passes (): bool = let
  val dir = "build/verify-tests/namespace-matching-sidecar"
  val () = _base(dir)
  val () = _zip(dir, "wasm.bats-packages.dev/bridge", "new_2.bats", false)
  val () = _sidecar(dir, "wasm.bats-packages.dev/bridge", "new_2.bats", true)
  val () = _commit(dir, "change")
in _judge(dir, 0, "ok   wasm.bats-packages.dev/bridge/new_2.bats", "", "", "FAIL") end

(* A published archive that is modified fails *)
fn test_modified_archive_fails (): bool = let
  val dir = "build/verify-tests/modified-archive"
  val () = _base(dir)
  val () = _zip(dir, "pkg", "old_1.bats", false)
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: pkg/old_1.bats is M: published archives are never modified or removed", "", "", "ok   ") end

(* ... and one that is removed fails *)
fn test_removed_archive_fails (): bool = let
  val dir = "build/verify-tests/removed-archive"
  val () = _base(dir)
  val () = _remove(dir, "pkg", "old_1.bats")
  val () = _commit(dir, "change")
in _judge(dir, 1, "FAIL: pkg/old_1.bats is D: published archives are never modified or removed", "", "", "ok   ") end

(* The regression loop reports a package that passed at the base and fails at
   the head: the change adds a good archive and the file BROKEN, with which
   the stand-in's check fails for the package that depends on the repository *)
fn test_regression_is_reported (): bool = let
  val dir = "build/verify-tests/regression"
  val () = _base(dir)
  val () = _zip(dir, "other", "new_1.bats", false)
  val () = _sidecar(dir, "other", "new_1.bats", true)
  val () = _text(dir, ".", "BROKEN", "the repository now breaks its dependents\n")
  val () = _commit(dir, "change")
in _judge(dir, 1, "ok   other/new_1.bats", "FAIL: pkg/old_1.bats passed bats check before this change and fails after it", "BROKEN exists", "does not match") end

(* The same change without BROKEN passes: the loop's report above is the
   file's doing *)
fn test_no_regression_passes (): bool = let
  val dir = "build/verify-tests/no-regression"
  val () = _base(dir)
  val () = _zip(dir, "other", "new_1.bats", false)
  val () = _sidecar(dir, "other", "new_1.bats", true)
  val () = _commit(dir, "change")
in _judge(dir, 0, "ok   other/new_1.bats", "", "", "FAIL") end

end
