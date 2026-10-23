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
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val c = byte2int0($A.read<byte>(bytes, i))
  in
    if c > 32 && c < 127 && c <> 124 then _word_chars(bytes, i + 1, j) else false
  end

(* A name, kind or version: one or more printable ASCII bytes with no space
   and no '|' (which would end a table cell) *)
fn _word_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i < j then _word_chars(bytes, i, j) else false

fun _digits_only {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then true
  else let
    val c = byte2int0($A.read<byte>(bytes, i))
  in
    if c >= 48 && c <= 57 then _digits_only(bytes, i + 1, j) else false
  end

(* The age: 1 to 6 digits, with no leading zero unless it is the one digit *)
fn _age_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  if i >= j then false
  else if j - i > 6 then false
  else if ~_digits_only(bytes, i, j) then false
  else if j - i = 1 then true
  else byte2int0($A.read<byte>(bytes, i)) <> 48

fn _status_is {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j, status: move_status): bool =
  span_is(bytes, i, j, status_words(status))

(* Whether bytes[i, j) is the words of one of the four statuses *)
fn _status_ok {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (bytes: !$A.borrow(byte, l, n), i: int i, j: int j): bool =
  _status_is(bytes, i, j, Status_moved()) || _status_is(bytes, i, j, Status_major_not_moved())
  || _status_is(bytes, i, j, Status_too_new()) || _status_is(bytes, i, j, Status_current())

(* The line bytes[line_start, line_stop) as a table row appended to out, when it
   is a record: whether it is. The row is appended only when it is. *)
fn _render_line {l:agz}{n:pos}{line_stop:nat | line_stop <= n}
  {line_start:nat | line_start <= line_stop}
  (bytes: !$A.borrow(byte, l, n), line_start: int line_start, line_stop: int line_stop,
   out: !$B.sized_rope): bool = let
  val first_tab = find_byte(bytes, line_stop, line_start, 9)
in
  if first_tab >= line_stop then false
  else let
    val second_tab = find_byte(bytes, line_stop, first_tab + 1, 9)
  in
    if second_tab >= line_stop then false
    else let
      val third_tab = find_byte(bytes, line_stop, second_tab + 1, 9)
    in
      if third_tab >= line_stop then false
      else let
        val fourth_tab = find_byte(bytes, line_stop, third_tab + 1, 9)
      in
        if fourth_tab >= line_stop then false
        else let
          val fifth_tab = find_byte(bytes, line_stop, fourth_tab + 1, 9)
        in
          if fifth_tab >= line_stop then false
          else if find_byte(bytes, line_stop, fifth_tab + 1, 9) < line_stop then false
          else if ~_word_ok(bytes, line_start, first_tab) then false
          else if ~_word_ok(bytes, first_tab + 1, second_tab) then false
          else if ~_word_ok(bytes, second_tab + 1, third_tab) then false
          else if ~_word_ok(bytes, third_tab + 1, fourth_tab) then false
          else if ~_age_ok(bytes, fourth_tab + 1, fifth_tab) then false
          else if ~_status_ok(bytes, fifth_tab + 1, line_stop) then false
          else let
            val () = $B.sized_rope_bput(out, "| ")
            val () = $B.sized_rope_copy(out, bytes, line_start, first_tab)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, bytes, first_tab + 1, second_tab)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, bytes, second_tab + 1, third_tab)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, bytes, third_tab + 1, fourth_tab)
            val () = $B.sized_rope_bput(out, " | ")
            val () = $B.sized_rope_copy(out, bytes, fourth_tab + 1, fifth_tab)
            val () =
              if span_is(bytes, fourth_tab + 1, fifth_tab, "1")
              then $B.sized_rope_bput(out, " day | ")
              else $B.sized_rope_bput(out, " days | ")
            val () = $B.sized_rope_copy(out, bytes, fifth_tab + 1, line_stop)
            val () = $B.sized_rope_bput(out, " |\n")
          in true end
        end
      end
    end
  end
end

fun _render_lines {l:agz}{n:pos}{records_len:nat | records_len <= n}
  {i:nat | i <= records_len}{number:pos} .<records_len - i>.
  (bytes: !$A.borrow(byte, l, n), records_len: int records_len, i: int i,
   number: int number, out: !$B.sized_rope): [bad:nat] int bad =
  if i >= records_len then 0
  else let
    val line_stop = find_byte(bytes, records_len, i, 10)
  in
    if ~_render_line(bytes, i, line_stop, out) then number
    else if line_stop >= records_len then 0
    else _render_lines(bytes, records_len, line_stop + 1, number + 1, out)
  end

(* The table of the records in records[0, records_len), appended to out: the
   header and one row for each record, in order. The result is 0 when every line is a
   record, else the number (from 1) of the first line that is not, and the
   rows before it are in out (the caller discards them). Lines end at a
   newline, and the last needs none. No records is the header alone. *)
#pub fn render_table {l:agz}{n:pos}{records_len:nat | records_len <= n}
  (records: !$A.borrow(byte, l, n), records_len: int records_len, out: !$B.sized_rope)
  : [bad:nat] int bad

implement render_table (records, records_len, out) = let
  val () = $B.sized_rope_bput(out, "| Kind | Name | Old | New | Release age | Status |\n")
  val () = $B.sized_rope_bput(out, "| --- | --- | --- | --- | --- | --- |\n")
in _render_lines(records, records_len, 0, 1, out) end
