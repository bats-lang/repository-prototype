(* git_stand_in: the git of the skew case (area: relock heads), put on PATH under the name git;
   each ls-remote answer differs from the one before. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

fun _zeros {n:nat} .<n>. (n: int n): void =
  if n <= 0 then ()
  else let
    val () = print_int (0)
  in _zeros(n - 1) end

fun _width {k:nat} .<k>. (k: int k): [w:nat] int w =
  if k < 10 then 1 else 1 + _width(k / 10)

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
  val width = _width(calls_len)
  val () = print_int (calls_len)
  val () = if 40 > width then _zeros(40 - width) else ()
in print! ("\trefs/heads/main\n") end
