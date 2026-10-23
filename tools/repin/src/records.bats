(* records -- the move record and the table of repin (bats-lang/repository-
   prototype#410). Keyword: repin records.

   A move record is one line of tab-separated fields:

     kind TAB name TAB old TAB new TAB age TAB status

   one line for each pin examined. The kind is a plain word (action, npm,
   gradle, and any word a later kind brings: the record does not change for
   it); name, old and new are words of printable ASCII with no space and no
   '|'; age is the release age in whole days (digits, no leading zero); the
   status is one of the four words of move_status. The table is the records
   as the Markdown table of the relock pull request body. A line that is
   none of this is a bad record, named by its number, and no table is
   made. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

(* What became of the pin: it moved, a major version was found and the pin
   was not moved, the newer release is younger than 7 days, or there is no
   newer release. Every caller matches all four (case+). *)
#pub datatype move_status =
  | Status_moved
  | Status_major_not_moved
  | Status_too_new
  | Status_current

(* The status as the record and the table write it *)
#pub fn status_words (status: move_status): [n:nat] string n

implement status_words (status) =
  case+ status of
  | Status_moved() => "moved"
  | Status_major_not_moved() => "major, not moved"
  | Status_too_new() => "too new"
  | Status_current() => "current"

(* Appends the status words *)
#pub fn put_status (out: !$B.sized_rope, status: move_status): void

implement put_status (out, status) = $B.sized_rope_bput(out, status_words(status))

(* Appends the age in days as a record writes it: the digits *)
#pub fn put_age (out: !$B.sized_rope, days: int): void

implement put_age (out, days) = let
  var digits : $B.builder(0) = $B.create()
  val () = $B.put_int(digits, days)
  val @(chunk, used) = $B.to_arr(digits)
  val @(frozen, view) = $A.freeze<byte>(chunk)
  val () = $B.sized_rope_copy(out, view, 0, used)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in () end

(* Appends the age as words for a person: 1 day, 7 days *)
#pub fn put_days (out: !$B.sized_rope, days: int): void

implement put_days (out, days) = let
  val () = put_age(out, days)
in if days = 1 then $B.sized_rope_bput(out, " day") else $B.sized_rope_bput(out, " days") end

fun _word_chars {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (b: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val c = byte2int0($A.read<byte>(b, i))
  in
    if c > 32 && c < 127 && c <> 124 then _word_chars(b, i + 1, j) else false
  end

(* A name, kind or version: one or more printable ASCII bytes with no space
   and no '|' (which would end a table cell) *)
fn _word_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (b: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i < j then _word_chars(b, i, j) else false

fun _digits_only {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (b: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val c = byte2int0($A.read<byte>(b, i))
  in
    if c >= 48 && c <= 57 then _digits_only(b, i + 1, j) else false
  end

(* The age: 1 to 6 digits, with no leading zero unless it is the one digit *)
fn _age_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (b: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then false
  else if j - i > 6 then false
  else if ~_digits_only(b, i, j) then false
  else if j - i = 1 then true
  else byte2int0($A.read<byte>(b, i)) <> 48

fn _status_is {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (b: !$A.borrow(byte, l, n), i: int i, j: int j, status: move_status): bool =
  span_is(b, i, j, status_words(status))

(* Whether b[i, j) is the words of one of the four statuses *)
fn _status_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (b: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  _status_is(b, i, j, Status_moved()) || _status_is(b, i, j, Status_major_not_moved())
  || _status_is(b, i, j, Status_too_new()) || _status_is(b, i, j, Status_current())

(* The line b[line_start, line_stop) as a table row appended to out, when it
   is a record: whether it is. The row is appended only when it is. *)
fn _render_line {l:agz}{n:pos}{line_stop:nat | line_stop <= n}
  {line_start:nat | line_start <= line_stop}
  (b: !$A.borrow(byte, l, n), line_start: int line_start, line_stop: int line_stop,
   out: !$B.sized_rope): bool = let
  val t1 = find_byte(b, line_stop, line_start, 9)
in
  if t1 >= line_stop then false
  else let
    val t2 = find_byte(b, line_stop, t1 + 1, 9)
  in
    if t2 >= line_stop then false
    else let
      val t3 = find_byte(b, line_stop, t2 + 1, 9)
    in
      if t3 >= line_stop then false
      else let
        val t4 = find_byte(b, line_stop, t3 + 1, 9)
      in
        if t4 >= line_stop then false
        else let
          val t5 = find_byte(b, line_stop, t4 + 1, 9)
        in
          if t5 >= line_stop then false
          else if find_byte(b, line_stop, t5 + 1, 9) < line_stop then false
          else if ~_word_ok(b, line_start, t1) then false
          else if ~_word_ok(b, t1 + 1, t2) then false
          else if ~_word_ok(b, t2 + 1, t3) then false
          else if ~_word_ok(b, t3 + 1, t4) then false
          else if ~_age_ok(b, t4 + 1, t5) then false
          else if ~_status_ok(b, t5 + 1, line_stop) then false
          else let
            val () = $B.sized_rope_bput(out, "| ")
            val () = $B.sized_rope_copy(out, b, line_start, t1)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, b, t1 + 1, t2)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, b, t2 + 1, t3)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, b, t3 + 1, t4)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, b, t4 + 1, t5)
            val () = if span_is(b, t4 + 1, t5, "1") then $B.sized_rope_bput(out, " day | ")
                     else $B.sized_rope_bput(out, " days | ")
            val () = $B.sized_rope_copy(out, b, t5 + 1, line_stop)
            val () = $B.sized_rope_bput(out, " |\n")
          in true end
        end
      end
    end
  end
end

fun _render_lines {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{number:pos} .<k - i>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, number: int number, out: !$B.sized_rope)
  : [bad:nat] int bad =
  if i >= k then 0
  else let
    val line_stop = find_byte(b, k, i, 10)
  in
    if ~_render_line(b, i, line_stop, out) then number
    else if line_stop >= k then 0
    else _render_lines(b, k, line_stop + 1, number + 1, out)
  end

(* The table of the records in b[0, k), appended to out: the header and one
   row for each record, in order. The result is 0 when every line is a
   record, else the number (from 1) of the first line that is not, and the
   rows before it are in out (the caller discards them). Lines end at a
   newline, and the last needs none. No records is the header alone. *)
#pub fn render_table {l:agz}{n:pos}{k:nat | k <= n}
  (records: !$A.borrow(byte, l, n), k: int k, out: !$B.sized_rope): [bad:nat] int bad

implement render_table (records, k, out) = let
  val () = $B.sized_rope_bput(out, "| Kind | Name | Old | New | Release age | Status |\n")
  val () = $B.sized_rope_bput(out, "| --- | --- | --- | --- | --- | --- |\n")
in _render_lines(records, k, 0, 1, out) end
