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

fn _exists {sn:nat | sn < 4096} (path: string sn): bool = let
  var probe : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant(path, probe)
  val () = $B.builder_free(probe)
in
  case+ ended of
  | Read_whole() => true
  | Read_too_long() => true
  | Read_failed() => false
end

implement main0 () =
  if _exists("gh-fail") then exit_void(1)
  else if _exists("gh-flood") then _flood(8000)
  else let
    var names : $B.builder(0) = $B.create()
    val @(ended, _) = read_constant("gh-names.txt", names)
    val @(arr, k) = $B.to_arr(names)
    val @(fz, bv) = $A.freeze<byte>(arr)
    val () = print_range(bv, 0, k)
    val () = $A.drop<byte>(fz, bv)
    val () = $A.free<byte>($A.thaw<byte>(fz))
  in
    case+ ended of
    | Read_whole() => ()
    | Read_too_long() => exit_void(1)
    | Read_failed() => exit_void(1)
  end
