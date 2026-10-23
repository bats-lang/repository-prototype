(* gh_stand_in -- the `gh` of the audit's tests (bats-lang/repository-
   prototype#396): the test puts a copy of it named gh in a directory on
   PATH and runs the audit there. It prints the file gh-names.txt of its
   current directory, whatever its arguments; it exits 1 when the file
   gh-fail exists, and prints more than the audit's buffer holds when the
   file gh-flood exists. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

fun _flood {n:nat} .<n>. (n: int n): void =
  if n <= 0 then ()
  else let
    val () = print! ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n")
  in _flood(n - 1) end

implement main0 () =
  if constant_exists("gh-fail") then exit_void(1)
  else if constant_exists("gh-flood") then _flood(8000)
  else let
    var names : $B.builder(0) = $B.create()
    val @(ended, _) = read_constant("gh-names.txt", names)
    val @(arr, k) = $B.to_arr(names)
    val @(frozen, view) = $A.freeze<byte>(arr)
    val () = print_range(view, 0, k)
    val () = $A.drop<byte>(frozen, view)
    val () = $A.free<byte>($A.thaw<byte>(frozen))
  in
    case+ ended of
    | Read_whole() => ()
    | Read_too_long() => exit_void(1)
    | Read_failed() => exit_void(1)
  end
