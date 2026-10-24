(* gh_stand_in -- the `gh` of the audit's tests (bats-lang/repository-
   prototype#396): the test puts a copy of it named gh in a directory on
   PATH and runs the audit there. It prints the file gh-names.txt of its
   current directory, whatever its arguments; it exits 1 when the file
   gh-fail exists, and prints more than the audit's buffer holds when the
   file gh-flood exists. A call whose first argument is `issue` (the audit's
   tickets, bats-lang/repository-prototype#405) is appended to the file
   gh-calls.txt of its current directory as one line, its arguments joined
   by spaces (the last argument's zero byte is not one); `issue list` prints the file gh-open.txt (the numbers of the
   open tickets, one on each line) when it exists, and the other calls print
   a line `https://example.invalid/<verb>`. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use result as R

staload "support.sats"

fun _flood {n:nat} .<n>. (n: int n): void =
  if n <= 0 then ()
  else let
    val () = print! ("xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n")
  in _flood(n - 1) end

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

(* The call `gh issue <verb> ...`, its arguments args[0, args_len) and its verb from verb_start: recorded, and answered *)
fn _issue {l:agz}{n:pos}{args_len:nat | args_len <= n; args_len <= 4096}{verb_start:nat | verb_start <= args_len}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, verb_start: int verb_start): void = let
  var record : $B.builder(0) = $B.create()
  val () = _spaced(args, _without_last(args_len), 0, record)
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
  val verb_stop = find_byte(args, args_len, verb_start, 0)
in
  if line_is(args, verb_start, verb_stop, "list") then let
    var open : $B.builder(0) = $B.create()
    val @(_, _) = read_constant("gh-open.txt", open)
    val @(open_array, open_len) = $B.to_arr(open)
    val @(open_frozen, open_view) = $A.freeze<byte>(open_array)
    val () = print_range(open_view, 0, open_len)
    val () = $A.drop<byte>(open_frozen, open_view)
    val () = $A.free<byte>($A.thaw<byte>(open_frozen))
  in () end
  else let
    val () = print! ("https://example.invalid/")
    val () = print_range(args, verb_start, verb_stop)
  in println!() end
end

(* The list of the organisation's repositories *)
fn _names_answer (): void =
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

(* The place after the zero byte that ends the argument that starts at from, or the end *)
fn _after_first_from {l:agz}{n:pos}{args_len:nat | args_len <= n}{from:nat | from <= args_len}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, from: int from): [after:nat | after <= args_len] int after = let
  val stop = find_byte(args, args_len, from, 0)
in if stop >= args_len then args_len else stop + 1 end

(* The place of the argument after the program's own name *)
fn _after_first {l:agz}{n:pos}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): [after:nat | after <= args_len] int after =
  _after_first_from(args, args_len, 0)

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val args_len = (case+ $E.args_read(buffer, 4096) of | ~$R.some(count) => count | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(args_frozen, args_view) = $A.freeze<byte>(buffer)
  val second_start = _after_first(args_view, args_len)
  val second_stop = find_byte(args_view, args_len, second_start, 0)
  val is_issue = line_is(args_view, second_start, second_stop, "issue")
  val () =
    if is_issue then _issue(args_view, args_len, _after_first_from(args_view, args_len, second_start))
    else ()
  val () = $A.drop<byte>(args_frozen, args_view)
  val () = $A.free<byte>($A.thaw<byte>(args_frozen))
in
  if is_issue then () else _names_answer()
end
