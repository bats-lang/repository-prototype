(* git_stand_in -- the `git ls-remote` of relock-pins-test.yml's skew case
   (bats-lang/repository-prototype#494, area: relock heads): the test puts a
   copy of it named git in a directory on PATH. Each call appends one byte to
   the file git-calls of its current directory and prints a line
   `<40 digits>\trefs/heads/main` whose digit is the number of calls so far
   (modulo ten), so the main it answers moves at every call. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

fun _digits {n:nat} .<n>. (digit: int, n: int n): void =
  if n <= 0 then ()
  else let
    val () = print_int (digit)
  in _digits(digit, n - 1) end

implement main0 () = let
  var call_path : $B.builder(0) = $B.create()
  val () = $B.bput(call_path, "git-calls")
  val @(call_array, call_len) = $B.to_arr(call_path)
  val @(call_frozen, call_view) = $A.freeze<byte>(call_array)
  var mark : $B.builder(0) = $B.create()
  val () = $B.bput(mark, "x")
  val @(mark_array, mark_len) = $B.to_arr(mark)
  val @(mark_frozen, mark_view) = $A.freeze<byte>(mark_array)
  val _ = write_file(call_view, call_len, mark_view, mark_len, true)
  val () = $A.drop<byte>(mark_frozen, mark_view)
  val () = $A.free<byte>($A.thaw<byte>(mark_frozen))
  val () = $A.drop<byte>(call_frozen, call_view)
  val () = $A.free<byte>($A.thaw<byte>(call_frozen))
  var calls : $B.builder(0) = $B.create()
  val @(_, _) = read_constant("git-calls", calls)
  val @(calls_array, calls_len) = $B.to_arr(calls)
  val () = $A.free<byte>(calls_array)
  val () = _digits(calls_len % 10, 40)
in print! ("\trefs/heads/main\n") end
