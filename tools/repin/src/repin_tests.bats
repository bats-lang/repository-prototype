(* repin_tests -- the tests of repin (bats-lang/repository-prototype#410), run
   by `bats test` in tools/repin. Each case builds its input in memory and
   compares the output byte for byte with a literal; `now` is a constant of
   each case, never the clock, and no file is read. Keyword: repin tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "age.sats"
staload "records.sats"
staload "support.sats"

(* ============================================================
   Comparing a rope with a literal
   ============================================================ *)

(* The length of a text *)
fn text_length {text_len:nat} (text: string text_len): int text_len = g1u2i(string1_length(text))

(* Whether the chunk's bytes[i, used) are the literal from at on *)
fun _equal_from {l:agz}{n:pos}{used:nat | used <= n}{i:nat | i <= used}{literal_len:nat}
  {at:nat | at + (used - i) <= literal_len} .<used - i>.
  (bytes: !$A.borrow(byte, l, n), used: int used, i: int i, literal: string literal_len,
   at: int at): bool =
  if i >= used then true
  else if byte2int0($A.read<byte>(bytes, i)) = char2int0(string_get_at(literal, at)) then
    _equal_from(bytes, used, i + 1, literal, at + 1)
  else false

fun _chunks_are {k:nat}{literal_len:nat}{at:nat | at <= literal_len} .<k>.
  (chunks: $B.rope_sized_list(k), literal: string literal_len, literal_len: int literal_len,
   at: int at): bool =
  case+ chunks of
  | ~$B.rope_sized_nil() => at = literal_len
  | ~$B.rope_sized_cons(chunk, used, rest) =>
    if at + used <= literal_len then let
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val same = _equal_from(view, used, 0, literal, at)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
    in
      if same then _chunks_are(rest, literal, literal_len, at + used)
      else let val () = $B.rope_sized_list_free(rest) in false end
    end
    else let
      val () = $A.free<byte>(chunk)
      val () = $B.rope_sized_list_free(rest)
    in false end

(* Whether the rope's text is exactly the literal *)
fn _rope_is {literal_len:nat} (text: $B.sized_rope, literal: string literal_len): bool =
  _chunks_are($B.sized_rope_chunks(text), literal, text_length(literal), 0)

(* ============================================================
   The table of a records text
   ============================================================ *)

(* The table of the records, and the number of the first bad line (0 when
   there is none), compared with the expected table *)
fn _table_is {records_len,expected_len:nat | records_len < 4096}
  (records: string records_len, expected: string expected_len): bool = let
  var text : $B.builder(0) = $B.create()
  val () = $B.bput(text, records)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(frozen, view) = $A.freeze<byte>(text_array)
  val table = $B.sized_rope_create()
  val bad = render_table(view, text_len, table)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if bad = 0 then _rope_is(table, expected)
  else let val () = discard_rope(table) in false end
end

(* The number of the first line of the records that is not a record *)
fn _bad_line {records_len:nat | records_len < 4096} (records: string records_len): int = let
  var text : $B.builder(0) = $B.create()
  val () = $B.bput(text, records)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(frozen, view) = $A.freeze<byte>(text_array)
  val table = $B.sized_rope_create()
  val bad = render_table(view, text_len, table)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
  val () = discard_rope(table)
in bad end

(* A fixed now, as seconds since the epoch: 2026-10-23 *)
fn _now (): lint = 1792800000L

fn _seconds_are {text_len:nat | text_len < 4096}
  (text: string text_len, ok: bool, value: lint): bool = let
  var builder : $B.builder(0) = $B.create()
  val () = $B.bput(builder, text)
  val @(array, used) = $B.to_arr(builder)
  val @(frozen, view) = $A.freeze<byte>(array)
  val @(parsed, parsed_value) = parse_seconds(view, 0, used)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in if ok then parsed && parsed_value = value else ~parsed end

(* Whether the writer of a status gives the words *)
fn _status_is {words_len:nat} (status: move_status, words: string words_len): bool = let
  val out = $B.sized_rope_create()
  val () = put_status(out, status)
in _rope_is(out, words) end

(* Whether the writer of an age gives the digits *)
fn _age_is {digits_len:nat} (days: int, digits: string digits_len): bool = let
  val out = $B.sized_rope_create()
  val () = put_age(out, days)
in _rope_is(out, digits) end

(* Whether the writer of an age in words gives them *)
fn _days_are {words_len:nat} (days: int, words: string words_len): bool = let
  val out = $B.sized_rope_create()
  val () = put_days(out, days)
in _rope_is(out, words) end

$UNITTEST.run begin

(* ============================================================
   The age rule
   ============================================================ *)

(* 6 days 23 hours 59 minutes 59 seconds is not a candidate *)
fn test_age_just_under_seven_days_is_not_a_candidate (): bool =
  ~is_candidate(_now(), _now() - (6L * 86400L + 23L * 3600L + 59L * 60L + 59L))

(* exactly 7 days (604800 seconds) is a candidate *)
fn test_age_exactly_seven_days_is_a_candidate (): bool =
  is_candidate(_now(), _now() - 604800L)

(* 30 days is a candidate *)
fn test_age_thirty_days_is_a_candidate (): bool =
  is_candidate(_now(), _now() - 30L * 86400L)

(* A release published at now, and one published after now, are not *)
fn test_age_zero_and_future_are_not_candidates (): bool =
  ~is_candidate(_now(), _now()) && ~is_candidate(_now(), _now() + 1L)
  && ~is_candidate(_now(), _now() + 10L * 86400L)

(* The minimum is 7 days, and the rule is the minimum *)
fn test_age_minimum_is_seven_days (): bool =
  minimum_age_seconds() = 7L * 86400L

(* Whole days, rounded down; 0 for the future *)
fn test_age_days_are_whole_days_rounded_down (): bool =
  age_days(_now(), _now() - (6L * 86400L + 86399L)) = 6
  && age_days(_now(), _now() - 604800L) = 7
  && age_days(_now(), _now() - 30L * 86400L) = 30
  && age_days(_now(), _now() - 86399L) = 0
  && age_days(_now(), _now() - 86400L) = 1
  && age_days(_now(), _now() + 5L) = 0

(* The same rule at 2^31 seconds and after: no year 2038 *)
fn test_age_after_the_year_2038 (): bool =
  is_candidate(2200000000L, 2200000000L - 604800L)
  && ~is_candidate(2200000000L, 2200000000L - 604799L)

(* ============================================================
   Whole seconds
   ============================================================ *)

fn test_seconds_one_to_twelve_digits (): bool =
  _seconds_are("0", true, 0L) && _seconds_are("1792800000", true, 1792800000L)
  && _seconds_are("999999999999", true, 999999999999L)

fn test_seconds_otherwise_are_refused (): bool =
  _seconds_are("", false, 0L) && _seconds_are("1000000000000", false, 0L)
  && _seconds_are("12a", false, 0L) && _seconds_are("-1", false, 0L)
  && _seconds_are(" 1", false, 0L) && _seconds_are("1.5", false, 0L)

(* ============================================================
   The writers of a record
   ============================================================ *)

fn test_status_words (): bool =
  _status_is(Status_moved(), "moved")
  && _status_is(Status_major_not_moved(), "major, not moved")
  && _status_is(Status_too_new(), "too new")
  && _status_is(Status_current(), "current")

fn test_age_written_as_digits_and_as_words (): bool =
  _age_is(0, "0") && _age_is(30, "30") && _days_are(1, "1 day") && _days_are(7, "7 days")

(* ============================================================
   The table
   ============================================================ *)

(* One row of each status, and one of each kind, byte for byte *)
fn test_table_one_row_of_each_status (): bool =
  _table_is(
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n\
npm\t@playwright/test\t1.55.0\t2.0.0\t30\tmajor, not moved\n\
gradle\tcom.android.tools.build:gradle\t9.0.0\t9.0.1\t3\ttoo new\n\
action\tactions/setup-node\tv4.1.0\tv4.1.0\t1\tcurrent\n",
    "| Kind | Name | Old | New | Release age | Status |\n\
| --- | --- | --- | --- | --- | --- |\n\
| action | actions/checkout | v4.4.0 | v4.5.0 | 12 days | moved |\n\
| npm | @playwright/test | 1.55.0 | 2.0.0 | 30 days | major, not moved |\n\
| gradle | com.android.tools.build:gradle | 9.0.0 | 9.0.1 | 3 days | too new |\n\
| action | actions/setup-node | v4.1.0 | v4.1.0 | 1 day | current |\n")

(* A kind is a plain word: a kind a later piece brings changes nothing *)
fn test_table_any_kind_word (): bool =
  _table_is("pwa-ref\tbats-lang/pwa\ta1b2c3d\te4f5a6b\t0\tcurrent\n",
    "| Kind | Name | Old | New | Release age | Status |\n\
| --- | --- | --- | --- | --- | --- |\n\
| pwa-ref | bats-lang/pwa | a1b2c3d | e4f5a6b | 0 days | current |\n")

(* No records is the header alone; the last line needs no newline *)
fn test_table_header_alone_and_no_final_newline (): bool =
  _table_is("", "| Kind | Name | Old | New | Release age | Status |\n\
| --- | --- | --- | --- | --- | --- |\n")
  && _table_is("npm\ta\t1\t2\t7\tmoved",
    "| Kind | Name | Old | New | Release age | Status |\n\
| --- | --- | --- | --- | --- | --- |\n\
| npm | a | 1 | 2 | 7 days | moved |\n")

(* ============================================================
   What is not a record
   ============================================================ *)

fn test_bad_record_is_named_by_its_line (): bool =
  _bad_line("action\ta\t1\t2\t7\tmoved\n") = 0
  && _bad_line("action\ta\t1\t2\t7\tmoved\nnpm\tb\t1\t2\t7\tmoved\n") = 0
  && _bad_line("action\ta\t1\t2\t7\tmoved\nnpm\tb\t1\t2\t7\tnope\n") = 2
  && _bad_line("action\ta\t1\t2\t7\tmoved\nnpm\tb\t1\t2\t7\tmoved\ngradle\tc\n") = 3

fn test_bad_record_wrong_number_of_fields (): bool =
  _bad_line("action\ta\t1\t2\t7\n") = 1
  && _bad_line("action\ta\t1\t2\t7\tmoved\textra\n") = 1
  && _bad_line("\n") = 1
  && _bad_line("action\ta\t1\t2\t7\tmoved\n\naction\ta\t1\t2\t7\tmoved\n") = 2

fn test_bad_record_empty_or_unsafe_word (): bool =
  _bad_line("\ta\t1\t2\t7\tmoved\n") = 1
  && _bad_line("action\t\t1\t2\t7\tmoved\n") = 1
  && _bad_line("action\ta b\t1\t2\t7\tmoved\n") = 1
  && _bad_line("action\ta|b\t1\t2\t7\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t7\tmoved\r\n") = 1

fn test_bad_record_age (): bool =
  _bad_line("action\ta\t1\t2\t\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t07\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t-1\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t7d\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t1234567\tmoved\n") = 1
  && _bad_line("action\ta\t1\t2\t0\tmoved\n") = 0
  && _bad_line("action\ta\t1\t2\t999999\tmoved\n") = 0

fn test_bad_record_status_words_are_exact (): bool =
  _bad_line("action\ta\t1\t2\t7\tMoved\n") = 1
  && _bad_line("action\ta\t1\t2\t7\tmajor,not moved\n") = 1
  && _bad_line("action\ta\t1\t2\t7\ttoo  new\n") = 1
  && _bad_line("action\ta\t1\t2\t7\tcurrent \n") = 1
  && _bad_line("action\ta\t1\t2\t7\t\n") = 1

end
