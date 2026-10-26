(* skew_check: the skew case of relock-pins-test.yml (area: relock heads); it works in the current directory. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use list as L
#use process as P
#use result as R

staload "support.sats"

(* The place after the zero byte that ends the argument that starts at from, or the end *)
fn _after {l:agz}{n:pos}{args_len:nat | args_len <= n}{from:nat | from <= args_len}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, from: int from): [after:nat | after <= args_len] int after = let
  val stop = find_byte(args, args_len, from, 0)
in if stop >= args_len then args_len else stop + 1 end

fn _fail (message: string): void = let
  val () = println! (message)
in exit_void(1) end

fn _must (status: int, message: string): void =
  if status = 0 then () else _fail(message)

(* The text of relock-pins.yml between the markers of the pin moves, written to moves.sh *)
val _extract_program = "/# pin-moves end/ { on = 0 } on { print } /# pin-moves begin/ { on = 1 }"

fn _write_moves {l:agz}{n:pos | n <= 4096}{from,stop:nat | from <= stop; stop <= n}
  (args: !$A.borrow(byte, l, n), from: int from, stop: int stop): void = let
  var moves : $B.builder(0) = $B.create()
  val @(status, ended) = capture_with("awk",
    $L.list_vt_cons(arg_text("awk"), args2(arg_text(_extract_program), arg_range("", args, from, stop, ""))),
    no_arguments(), moves)
  val @(moves_array, moves_len) = $B.to_arr(moves)
  val @(moves_frozen, moves_view) = $A.freeze<byte>(moves_array)
  var moves_path : $B.builder(0) = $B.create()
  val () = $B.bput(moves_path, "moves.sh")
  val @(path_array, path_len) = $B.to_arr(moves_path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val written = write_file(path_view, path_len, moves_view, moves_len, false)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val () = $A.drop<byte>(moves_frozen, moves_view)
  val () = $A.free<byte>($A.thaw<byte>(moves_frozen))
  val () = _must(status, "::error::awk could not read the workflow")
  val () = (case+ ended of | Read_whole() => () | Read_too_long() => _fail("::error::the pin moves are longer than the buffer") | Read_failed() => _fail("::error::reading the pin moves failed"))
  val () = if moves_len > 0 then () else _fail("::error::no pin-moves program in the workflow")
in if written then () else _fail("::error::moves.sh was not written") end

(* The number of calls the stand-in git recorded *)
fn _calls (): int = let
  var calls : $B.builder(0) = $B.create()
  val @(_, _) = read_constant("git-calls", calls)
  val @(calls_array, calls_len) = $B.to_arr(calls)
  val () = $A.free<byte>(calls_array)
in calls_len end

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val args_len = (case+ $E.args_read(buffer, 4096) of | ~$R.some(count) => count | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(args_frozen, args) = $A.freeze<byte>(buffer)
  val workflow_start = _after(args, args_len, 0)
  val workflow_stop = find_byte(args, args_len, workflow_start, 0)
  val fixture_start = _after(args, args_len, workflow_start)
  val fixture_stop = find_byte(args, args_len, fixture_start, 0)
  val stand_in_start = _after(args, args_len, fixture_start)
  val stand_in_stop = find_byte(args, args_len, stand_in_start, 0)
  val () = _must(run_program("mkdir", args4(arg_text("-p"), arg_text("bin"), arg_text("home/relock"), arg_text("workflows"))), "::error::mkdir failed")
  val () = _must(run_program("cp", args2(arg_range("", args, fixture_start, fixture_stop, "/workflows/caller.yml"), arg_text("workflows/caller.yml"))), "::error::the fixture was not copied")
  val () = _must(run_program("cp", args2(arg_range("", args, stand_in_start, stand_in_stop, ""), arg_text("bin/git"))), "::error::the stand-in git was not copied")
  val () = _write_moves(args, workflow_start, workflow_stop)
  val environment = $L.list_vt_cons(arg_text("PATH=bin:/usr/local/bin:/usr/bin:/bin"),
    $L.list_vt_cons(arg_text("HOME=home"),
    $L.list_vt_cons(arg_text("GITHUB_REPOSITORY=bats-lang/skew"),
    args3(arg_text("WORKFLOWS_DIRECTORY=workflows"),
      arg_text("PINS=bats-lang/repository-prototype/.github/workflows/package-check.yml\nbats-lang/repository-prototype/.github/workflows/publish.yml\nbats-lang/bats/.github/actions/setup"),
      arg_text("PIN_COPIES=bats-lang/repository-prototype/.github/workflows/package-check.yml pwa-ref\nbats-lang/repository-prototype/.github/workflows/publish.yml pwa-ref")))))
  val () = _must(run_with("bash", $L.list_vt_cons(arg_text("bash"), args2(arg_text("-eu"), arg_text("moves.sh"))), environment), "::error::the pin moves failed")
  val same = run_with("cmp", $L.list_vt_cons(arg_text("cmp"), args2(arg_text("workflows/caller.yml"), arg_range("", args, fixture_start, fixture_stop, "/workflows/expected.yml"))), no_arguments())
  val () =
    if same = 0 then ()
    else let
      val () = println! ("::error::the pins and copies of one repository do not agree")
      val _ = run_program("diff", args3(arg_text("-u"), arg_range("", args, fixture_start, fixture_stop, "/workflows/expected.yml"), arg_text("workflows/caller.yml")))
    in exit_void(1) end
  val calls = _calls()
  val () = if calls = 2 then () else let
      val () = println! ("::error::", calls, " ls-remote calls for two repositories, expected 2")
    in exit_void(1) end
  val () = println! (calls, " ls-remote calls for 2 repositories; both repository-prototype pins and both pwa-ref copies hold one commit")
  val _ = run_program("cat", args1(arg_text("workflows/caller.yml")))
  val () = $A.drop<byte>(args_frozen, args)
  val () = $A.free<byte>($A.thaw<byte>(args_frozen))
in () end
