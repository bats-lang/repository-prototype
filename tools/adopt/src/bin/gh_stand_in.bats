(* gh_stand_in -- the `gh` of adopt's tests (bats-lang/repository-prototype#607):
   the test puts a copy of it named gh in a directory on PATH and runs adopt
   there. Every call is appended to the file gh-calls.txt of its current
   directory as one line, its arguments joined by spaces (the last
   argument's zero byte is not one). It exits 1 when the file gh-fail
   exists; else for `gh pr create` it prints the address of a pull request,
   https://example.invalid/pull/1, and for any other call nothing. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use result as R

staload "support.sats"

(* args[at, stop) written to out, a zero byte as a space *)
fun _spaced {l:agz}{n:pos}{stop:nat | stop <= n}{at:nat | at <= stop}{m:nat | m + (stop - at) <= 524288} .<stop - at>.
  (args: !$A.borrow(byte, l, n), stop: int stop, at: int at, out: !$B.builder(m) >> $B.builder(m + (stop - at))): void =
  if at >= stop then ()
  else let
    val byte_value = byte2int0($A.read<byte>(args, at))
    val () = $B.put_char(out, $AR.low_byte(if byte_value = 0 then 32 else byte_value))
  in _spaced(args, stop, at + 1, out) end

(* The length without the zero byte that ends the last argument *)
fn _without_last {len:nat | len <= 4096} (len: int len): [shorter:nat | shorter <= len] int shorter =
  if len > 0 then len - 1 else 0

(* The place after the zero byte that ends the argument that starts at from, or the end *)
fn _after_first_from {l:agz}{n:pos}{args_len:nat | args_len <= n}{from:nat | from <= args_len}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, from: int from): [after:nat | after <= args_len] int after = let
  val stop = find_byte(args, args_len, from, 0)
in if stop >= args_len then args_len else stop + 1 end

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val [args_len:int] args_len = (case+ $E.args_read(buffer, 4096) of | ~$R.some(count) => count | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(args_frozen, args_view) = $A.freeze<byte>(buffer)
  var record : $B.builder(0) = $B.create()
  val () = _spaced(args_view, _without_last(args_len), 0, record)
  val () = $B.bput(record, "\n")
  val @(record_array, record_len) = $B.to_arr(record)
  val @(record_frozen, record_view) = $A.freeze<byte>(record_array)
  var calls_path : $B.builder(0) = $B.create()
  val () = $B.bput(calls_path, "gh-calls.txt")
  val @(calls_array, calls_len) = $B.to_arr(calls_path)
  val @(calls_frozen, calls_view) = $A.freeze<byte>(calls_array)
  val _ = write_file(calls_view, calls_len, record_view, record_len, true)
  val () = $A.drop<byte>(calls_frozen, calls_view)
  val () = $A.free<byte>($A.thaw<byte>(calls_frozen))
  val () = $A.drop<byte>(record_frozen, record_view)
  val () = $A.free<byte>($A.thaw<byte>(record_frozen))
  val second_start = _after_first_from(args_view, args_len, 0)
  val second_stop = find_byte(args_view, args_len, second_start, 0)
  val third_start = _after_first_from(args_view, args_len, second_start)
  val third_stop = find_byte(args_view, args_len, third_start, 0)
  val is_create = line_is(args_view, second_start, second_stop, "pr") && line_is(args_view, third_start, third_stop, "create")
  val () = $A.drop<byte>(args_frozen, args_view)
  val () = $A.free<byte>($A.thaw<byte>(args_frozen))
in
  if constant_exists("gh-fail") then exit_void(1)
  else if is_create then println! ("https://example.invalid/pull/1")
  else ()
end
