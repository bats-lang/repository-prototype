(* sizes -- exact sizes for repin members-check (bats-lang/repository-prototype#466).
   Keyword: repin path rule.

   The cap and the sizes of a tar's members are decimal digit strings of any length, as the
   Python's int is, and are never converted to a number. The code keeps the room left,
   cap - total, as the ASCII digits of an array of 8200 bytes that holds, after the 8192 bytes
   of a listing line, the digits right-aligned with leading zeros. A listing line is at most
   8192 bytes, so a size has at most 8192 digits; there are at most 100000 members, so a
   total is below 10^8197 and has at most 8197 digits; a cap with more than 8200 significant
   digits is larger than every total a tar of this program can reach, so it is unlimited. A
   size is compared with the room by its significant digits (the leading zeros stripped, then
   the length, then the digits) and subtracted from it with a borrow. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR

(* The line region is arr[0, 8192); the room is arr[8192, 16392) *)

fun _fill_zeros {la:agz}{i:nat | i <= 16392} .<16392 - i>.
  (arr: !$A.arr(byte, la, 16392), i: int i): void =
  if i >= 16392 then ()
  else let
    val () = $A.set<byte>(arr, i, $A.int2byte(48))
  in _fill_zeros(arr, i + 1) end

(* The first place of the digits bytes[i, stop) that is not a zero, or stop *)
fun _args_first_nonzero {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i): [j:nat | i <= j; j <= stop] int j =
  if i >= stop then i
  else if byte2int0($A.read<byte>(bytes, i)) != 48 then i
  else _args_first_nonzero(bytes, stop, i + 1)

fun _copy_digits {la,l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop}
  {dest:nat | dest + (stop - i) <= 16392} .<stop - i>.
  (arr: !$A.arr(byte, la, 16392), bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i,
   dest: int dest): void =
  if i >= stop then ()
  else let
    val () = $A.set<byte>(arr, dest, $A.read<byte>(bytes, i))
  in _copy_digits(arr, bytes, stop, i + 1, dest + 1) end

(* The room made from the cap, the digits bytes[cap_start, cap_stop): whether the cap is
   unlimited (more than 8200 significant digits), and where the significant digits of the room
   start (16392 when it is 0 or unlimited) *)
#pub fn room_init {la,l:agz}{n:pos}{cap_stop:nat | cap_stop <= n}{cap_start:nat | cap_start <= cap_stop}
  (arr: !$A.arr(byte, la, 16392), bytes: !$A.borrow(byte, l, n), cap_start: int cap_start,
   cap_stop: int cap_stop): [s:nat | 8192 <= s; s <= 16392] @(bool, int s)

implement room_init (arr, bytes, cap_start, cap_stop) = let
  val first = _args_first_nonzero(bytes, cap_stop, cap_start)
  val digits = cap_stop - first
in
  if digits > 8200 then @(true, 16392)
  else let
    val () = _fill_zeros(arr, 8192)
    val () = _copy_digits(arr, bytes, cap_stop, first, 16392 - digits)
  in @(false, 16392 - digits) end
end

(* The first place of arr[i, stop) that holds a digit other than '0', or stop *)
fun _first_nonzero {la:agz}{stop:nat | stop <= 16392}{i:nat | i <= stop} .<stop - i>.
  (arr: !$A.arr(byte, la, 16392), stop: int stop, i: int i): [j:nat | i <= j; j <= stop] int j =
  if i >= stop then i
  else if byte2int0($A.get<byte>(arr, i)) != 48 then i
  else _first_nonzero(arr, stop, i + 1)

(* Whether the size digits arr[size, size + count) are at most the room digits
   arr[room, room + count) (the same count of significant digits) *)
fun _at_most {la:agz}{count:nat}{size:nat | size + count <= 16392}{room:nat | room + count <= 16392}
  {i:nat | i <= count} .<count - i>.
  (arr: !$A.arr(byte, la, 16392), size: int size, room: int room, count: int count, i: int i): bool =
  if i >= count then true
  else let
    val size_digit = byte2int0($A.get<byte>(arr, size + i))
    val room_digit = byte2int0($A.get<byte>(arr, room + i))
  in
    if size_digit < room_digit then true
    else if size_digit > room_digit then false
    else _at_most(arr, size, room, count, i + 1)
  end

(* The digit at distance k from the right end of the size digits that end at size_stop, or '0'
   past their start *)
fn _size_digit {la:agz}{size_start:nat}{size_stop:nat | size_start <= size_stop; size_stop <= 16392}
  {k:nat}
  (arr: !$A.arr(byte, la, 16392), size_start: int size_start, size_stop: int size_stop, k: int k): int =
  if size_stop - k - 1 >= size_start then byte2int0($A.get<byte>(arr, size_stop - k - 1)) - 48
  else 0

(* The size digits arr[size_start, size_stop) subtracted from the room, from the right
   (k is the distance from the right end), with the borrow; at most 8200 places *)
fun _subtract {la:agz}{size_start:nat}{size_stop:nat | size_start <= size_stop; size_stop <= 16392}
  {k:nat | k <= 8200} .<8200 - k>.
  (arr: !$A.arr(byte, la, 16392), size_start: int size_start, size_stop: int size_stop,
   k: int k, borrow: int): void =
  if k >= 8200 then ()
  else if size_stop - k - 1 < size_start && borrow = 0 then ()
  else let
    val room_digit = byte2int0($A.get<byte>(arr, 16391 - k)) - 48
    val taken = _size_digit(arr, size_start, size_stop, k) + borrow
    val under = room_digit < taken
    val result = (if under then room_digit + 10 - taken else room_digit - taken): int
    val () = $A.set<byte>(arr, 16391 - k, $A.int2byte($AR.low_byte(48 + result)))
  in _subtract(arr, size_start, size_stop, k + 1, (if under then 1 else 0)) end

(* The size, the digits arr[size_start, size_stop) of the line region, taken from the room
   whose significant digits start at room_start: whether it is at most the room (compared by
   the length of its significant digits and then the digits), and the room after (the same
   when it is over) *)
#pub fn room_take {la:agz}{size_start:nat}{size_stop:nat | size_start <= size_stop; size_stop <= 8192}
  {room_start:nat | 8192 <= room_start; room_start <= 16392}
  (arr: !$A.arr(byte, la, 16392), size_start: int size_start, size_stop: int size_stop,
   room_start: int room_start): [s:nat | 8192 <= s; s <= 16392] @(bool, int s)

fn _take_from {la:agz}{size_start:nat}{size_stop:nat | size_start <= size_stop; size_stop <= 8192}
  {room_start:nat | 8192 <= room_start; room_start <= 16392}
  (arr: !$A.arr(byte, la, 16392), first: int size_start, size_stop: int size_stop,
   room_start: int room_start): [s:nat | 8192 <= s; s <= 16392] @(bool, int s) = let
  val () = _subtract(arr, first, size_stop, 0, 0)
  val start = _first_nonzero(arr, 16392, room_start)
in @(true, start) end

implement room_take (arr, size_start, size_stop, room_start) = let
  val first = _first_nonzero(arr, size_stop, size_start)
  val significant = size_stop - first
  val room_digits = 16392 - room_start
in
  if significant <= 0 then @(true, room_start)
  else if significant > room_digits then @(false, room_start)
  else if significant = room_digits then
    (if _at_most(arr, first, room_start, significant, 0)
     then _take_from(arr, first, size_stop, room_start)
     else @(false, room_start))
  else _take_from(arr, first, size_stop, room_start)
end
