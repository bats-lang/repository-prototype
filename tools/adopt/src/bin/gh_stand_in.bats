(* gh_stand_in -- the `gh` of adopt's tests (bats-lang/repository-prototype#607):
   the test puts a copy of it named gh in a directory on PATH and runs adopt
   there. Every call is appended to the file gh-calls.txt of its current
   directory as one line, its arguments joined by spaces (the last
   argument's zero byte is not one). It exits 1 when the file gh-fail
   exists, and for `gh pr create` (GraphQL, which the real environment
   refuses, #611). For a call with -X POST (the REST call that opens a pull
   request) it prints the address of a pull request,
   https://example.invalid/pull/1, and keeps it in the file gh-pulls; for a
   call with -X GET it prints the file gh-pulls (nothing when there is
   none: no open pull request); for any other call nothing. *)

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

(* The pull request the POST opened, kept in the file gh-pulls so the next list (GET) shows it *)
fn _remember_pull (): void = let
  var path : $B.builder(0) = $B.create()
  val () = $B.bput(path, "gh-pulls")
  val @(path_array, path_len) = $B.to_arr(path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var text : $B.builder(0) = $B.create()
  val () = $B.bput(text, "https://example.invalid/pull/1\n")
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val _ = write_file(path_view, path_len, text_view, text_len, false)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in () end

(* The open pull requests: the file gh-pulls, if there is one *)
fn _print_pulls (): void = let
  var text : $B.builder(0) = $B.create()
  val @(_, _) = read_constant("gh-pulls", text)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val () = print_range(text_view, 0, text_len)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in () end

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
  val is_post = output_has(record_view, record_len, " -X POST ")
  val is_get = output_has(record_view, record_len, " -X GET ")
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
  else if is_create then exit_void(1)
  else if is_post then let
    val () = _remember_pull()
  in println! ("https://example.invalid/pull/1") end
  else if is_get then _print_pulls()
  else ()
end
