(* version -- release tags of repin (bats-lang/repository-prototype#411).
   Keyword: repin version.

   A version tag is an optional 'v' and one to eight numbers of one to nine
   digits, joined by '.': v4, v4.4.0, 4.4.0, v1.2.3.4. Nine digits is below
   2^31, so a number never overflows an int. Its major version is the first
   number. Two versions are compared number by number, a missing number
   being 0 (v4 and v4.0.0 are equal). A tag that is not of this shape (a
   prerelease such as v4.5.0-rc1, or a date) is not a version tag and is
   never a target of a move. *)

#include "share/atspre_staload.hats"

#use array as A

fun _digit_end {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): [k:nat | i <= k; k <= j] int k =
  if i >= j then i
  else let
    val digit = byte2int0($A.read<byte>(bytes, i))
  in
    if digit >= 48 && digit <= 57 then _digit_end(bytes, i + 1, j) else i
  end

fun _digits_value {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j, value: int): int =
  if i >= j then value
  else _digits_value(bytes, i + 1, j, value * 10 + byte2int0($A.read<byte>(bytes, i)) - 48)

(* Where the numbers start: after a 'v' when there is one *)
fn _numbers_start {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): [k:nat | i <= k; k <= j] int k =
  if i >= j then i
  else if byte2int0($A.read<byte>(bytes, i)) = 118 then i + 1
  else i

(* The numbers from i, which is before j: whether there are one to eight of one to nine
   digits, each but the last followed by a '.' and a number *)
fun _numbers_ok {l:agz}{n:pos}{i,j:nat | i < j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j, count: int): bool = let
  val stop = _digit_end(bytes, i, j)
in
  if stop = i then false
  else if stop - i > 9 then false
  else if stop >= j then true
  else if byte2int0($A.read<byte>(bytes, stop)) <> 46 then false
  else if stop + 1 >= j then false
  else if count >= 8 then false
  else _numbers_ok(bytes, stop + 1, j, count + 1)
end

(* Whether bytes[i, j) is a version tag *)
#pub fn version_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool

implement version_ok (bytes, i, j) = let
  val start = _numbers_start(bytes, i, j)
in
  if start < j then _numbers_ok(bytes, start, j, 1) else false
end

(* The major version of the version tag bytes[i, j) *)
#pub fn version_major {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): int

implement version_major (bytes, i, j) = let
  val start = _numbers_start(bytes, i, j)
in
  if start < j then let
    val stop = _digit_end(bytes, start, j)
  in _digits_value(bytes, start, stop, 0) end
  else 0
end

(* The number at i, which is before j, and where the next one starts (after the '.') *)
fn _number {l:agz}{n:pos}{i,j:nat | i < j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j)
  : [next:nat | i < next; next <= j] @(int, int next) = let
  val stop = _digit_end(bytes, i, j)
  val value = _digits_value(bytes, i, stop, 0)
in
  if stop < j then @(value, stop + 1) else @(value, j)
end

fun _compare_numbers {first_loc,second_loc:agz}{first_size,second_size:pos}
  {first_start,first_stop:nat | first_start <= first_stop; first_stop <= first_size}
  {second_start,second_stop:nat | second_start <= second_stop; second_stop <= second_size}
  .<(first_stop - first_start) + (second_stop - second_start)>.
  (first: !$A.borrow(byte, first_loc, first_size), first_start: int first_start,
   first_stop: int first_stop,
   second: !$A.borrow(byte, second_loc, second_size), second_start: int second_start,
   second_stop: int second_stop)
  : int =
  if first_start < first_stop then let
    val @(first_value, first_next) = _number(first, first_start, first_stop)
  in
    if second_start < second_stop then let
      val @(second_value, second_next) = _number(second, second_start, second_stop)
    in
      if first_value < second_value then ~1
      else if first_value > second_value then 1
      else _compare_numbers(first, first_next, first_stop, second, second_next, second_stop)
    end
    else if first_value > 0 then 1
    else _compare_numbers(first, first_next, first_stop, second, second_start, second_stop)
  end
  else if second_start < second_stop then let
    val @(second_value, second_next) = _number(second, second_start, second_stop)
  in
    if second_value > 0 then ~1
    else _compare_numbers(first, first_start, first_stop, second, second_next, second_stop)
  end
  else 0

(* ~1, 0 or 1 as the version tag first[first_start, first_stop) is less than, equal to or
   greater than second[second_start, second_stop); both are version tags *)
#pub fn version_compare {first_loc,second_loc:agz}{first_size,second_size:pos}
  {first_stop:nat | first_stop <= first_size}{first_start:nat | first_start <= first_stop}
  {second_stop:nat | second_stop <= second_size}{second_start:nat | second_start <= second_stop}
  (first: !$A.borrow(byte, first_loc, first_size), first_start: int first_start,
   first_stop: int first_stop,
   second: !$A.borrow(byte, second_loc, second_size), second_start: int second_start,
   second_stop: int second_stop): int

implement version_compare (first, first_start, first_stop, second, second_start, second_stop) =
  _compare_numbers(first, _numbers_start(first, first_start, first_stop), first_stop,
    second, _numbers_start(second, second_start, second_stop), second_stop)
