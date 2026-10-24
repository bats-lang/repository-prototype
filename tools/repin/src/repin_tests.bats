(* repin_tests -- the tests of repin (bats-lang/repository-prototype#410), run
   by `bats test` in tools/repin. Each case builds its input in memory and
   compares the output byte for byte with a literal; `now` is a constant of
   each case, never the clock, and no file is read. Keyword: repin tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use result as R

staload "actions.sats"
staload "age.sats"
staload "driver.sats"
staload "records.sats"
staload "support.sats"
staload "version.sats"

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

fun _chunks_are {chunk_count:nat}{literal_len:nat}{at:nat | at <= literal_len} .<chunk_count>.
  (chunks: $B.rope_sized_list(chunk_count), literal: string literal_len,
   literal_len: int literal_len,
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


(* ============================================================
   The action pins: in memory
   ============================================================ *)

(* The text as an array and its length, for a borrow: the caller frees it *)
fn _text_array {text_len:nat | text_len < 4096} (text: string text_len) = let
  var builder : $B.builder(0) = $B.create()
  val () = $B.bput(builder, text)
in $B.to_arr(builder) end

(* The text rewritten (at now) by the releases: whether there is no refused line, the
   text out, the records and whether a line changed are the expected ones *)
fn _rewrite_is {text_len,releases_len,out_len,records_len:nat | text_len < 4096; releases_len <
    4096}
  (text: string text_len, releases: string releases_len, now: lint,
   expected_text: string out_len, expected_records: string records_len, expected_changed: bool):
       bool = let
  val @(text_array, text_used) = _text_array(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val @(releases_array, releases_used) = _text_array(releases)
  val @(releases_frozen, releases_view) = $A.freeze<byte>(releases_array)
  val out = $B.sized_rope_create()
  val records = $B.sized_rope_create()
  val @(bad, changed) = rewrite_actions(text_view, text_used, releases_view, releases_used, now,
      out, records)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(releases_frozen, releases_view)
  val () = $A.free<byte>($A.thaw<byte>(releases_frozen))
  val same_text = _rope_is(out, expected_text)
  val same_records = _rope_is(records, expected_records)
in bad = 0 && same_text && same_records && changed = expected_changed end

(* The number of the first refused line of the text *)
fn _refused_line {text_len,releases_len:nat | text_len < 4096; releases_len < 4096}
  (text: string text_len, releases: string releases_len): int = let
  val @(text_array, text_used) = _text_array(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val @(releases_array, releases_used) = _text_array(releases)
  val @(releases_frozen, releases_view) = $A.freeze<byte>(releases_array)
  val out = $B.sized_rope_create()
  val records = $B.sized_rope_create()
  val @(bad, _) = rewrite_actions(text_view, text_used, releases_view, releases_used, _now(), out,
      records)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(releases_frozen, releases_view)
  val () = $A.free<byte>($A.thaw<byte>(releases_frozen))
  val () = discard_rope(out)
  val () = discard_rope(records)
in bad end

(* The number of the first line of the releases that is not a release line *)
fn _bad_release {releases_len:nat | releases_len < 4096} (releases: string releases_len): int = let
  val @(releases_array, releases_used) = _text_array(releases)
  val @(releases_frozen, releases_view) = $A.freeze<byte>(releases_array)
  val bad = validate_releases(releases_view, releases_used)
  val () = $A.drop<byte>(releases_frozen, releases_view)
  val () = $A.free<byte>($A.thaw<byte>(releases_frozen))
in bad end

fn _version_ok {text_len:nat | text_len < 4096} (text: string text_len): bool = let
  val @(array, used) = _text_array(text)
  val @(frozen, view) = $A.freeze<byte>(array)
  val ok = version_ok(view, 0, used)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in ok end

(* ~1, 0 or 1 as the version first is less than, equal to or greater than second *)
fn _version_compare {first_len,second_len:nat | first_len < 4096; second_len < 4096}
  (first: string first_len, second: string second_len): int = let
  val @(first_array, first_used) = _text_array(first)
  val @(first_frozen, first_view) = $A.freeze<byte>(first_array)
  val @(second_array, second_used) = _text_array(second)
  val @(second_frozen, second_view) = $A.freeze<byte>(second_array)
  val order = version_compare(first_view, 0, first_used, second_view, 0, second_used)
  val () = $A.drop<byte>(first_frozen, first_view)
  val () = $A.free<byte>($A.thaw<byte>(first_frozen))
  val () = $A.drop<byte>(second_frozen, second_view)
  val () = $A.free<byte>($A.thaw<byte>(second_frozen))
in order end

(* ============================================================
   The action pins: files
   ============================================================ *)

fun _copy_view {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m <= capacity}{i:nat | i <=
    m} .<m - i>.
  (source: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity), i:
      int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(source, i))
  in _copy_view(source, m, destination, i + 1) end

(* The text in an array of its length and extra more bytes (zero), the size file_mkdir and
   file_open take with extra = 1 *)
fn _exact_array {text_len,extra:nat | text_len < 4096; extra <= 1; text_len + extra > 0}
  (text: string text_len, extra: int extra): [l:agz] $A.arr(byte, l, text_len + extra) = let
  val @(source, used) = _text_array(text)
  val @(frozen, view) = $A.freeze<byte>(source)
  val destination = $A.alloc<byte>(used + extra)
  val () = _copy_view(view, used, destination, 0)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in destination end

(* The directory made; it may be there already *)
fn _mkdir {path_len:nat | path_len < 300} (path: string path_len): void = let
  val array = _exact_array(path, 1)
  val @(frozen, view) = $A.freeze<byte>(array)
  val () = $R.discard<int><$F.io_error>($F.file_mkdir(view, g1u2i(string1_length(path)) + 1, 493))
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in () end

(* The file made (or emptied) with the content, and given the permission bits mode *)
fn _make_file {path_len,content_len:nat | path_len < 300; content_len < 4096}
  (path: string path_len, content: string content_len, mode: int): void = let
  val array = _exact_array(path, 1)
  val @(frozen, view) = $A.freeze<byte>(array)
  val size = g1u2i(string1_length(path)) + 1
  val opened = $F.file_open(view, size, $F.WriteOnly(), $F.CreateOrTruncate(), 420)
  val () =
    (case+ opened of
     | ~$R.err(_) => ()
     | ~$R.ok(fd) => let
         val length = g1u2i(string1_length(content))
         val () =
           if length > 0 then let
             val piece = _exact_array(content, 0)
             val @(piece_frozen, piece_view) = $A.freeze<byte>(piece)
             val () = (case+ $F.file_write(fd, piece_view, length) of
                       | ~$R.ok(_) => ()
                       | ~$R.err(_) => ())
             val () = $A.drop<byte>(piece_frozen, piece_view)
             val () = $A.free<byte>($A.thaw<byte>(piece_frozen))
           in () end
           else ()
         val () = $R.discard<int><$F.io_error>($F.file_close(fd))
       in () end)
  val () = $R.discard<int><$F.io_error>($F.file_chmod(view, size, mode))
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in () end

(* The file's bytes are exactly the literal *)
fn _file_is {path_len,content_len:nat | path_len < 300; content_len < 4096}
  (path: string path_len, content: string content_len): bool = let
  val @(path_array, path_used) = _text_array(path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var text : $B.builder(0) = $B.create()
  val @(ended, _) = read_file(path_view, path_used, text)
  val @(text_array, text_used) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val rope = $B.sized_rope_create()
  val () = if text_used > 0 then $B.sized_rope_copy(rope, text_view, 0, text_used) else ()
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val same = _rope_is(rope, content)
in (case+ ended of Read_whole() => same | _ => false) end

(* The permission bits of the file *)
fn _mode_of {path_len:nat | path_len < 300} (path: string path_len): int = let
  val array = _exact_array(path, 1)
  val @(frozen, view) = $A.freeze<byte>(array)
  val mode = (case+ $F.file_mode(view, g1u2i(string1_length(path)) + 1) of
              | ~$R.ok(bits) => bits
              | ~$R.err(_) => ~1): int
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in mode end

(* `repin actions` over the directory with the releases file at now: its status and its
   records *)
fn _run {dir_len,releases_len:nat | dir_len < 300; releases_len < 300}
  (dir: string dir_len, releases: string releases_len, now: lint): @(int, $B.sized_rope) = let
  var arguments : $B.builder(0) = $B.create()
  val () = $B.bput(arguments, dir)
  val () = $B.bput(arguments, releases)
  val @(arguments_array, arguments_used) = $B.to_arr(arguments)
  val @(arguments_frozen, arguments_view) = $A.freeze<byte>(arguments_array)
  val records = $B.sized_rope_create()
  val status = run_actions(arguments_view, 0, g1u2i(string1_length(dir)),
    g1u2i(string1_length(dir)), arguments_used, now, records)
  val () = $A.drop<byte>(arguments_frozen, arguments_view)
  val () = $A.free<byte>($A.thaw<byte>(arguments_frozen))
in @(status, records) end

(* The records, written to a file and read back as `repin table` reads them, are the
   table (#410) *)
fn _records_table_is {table_len:nat | table_len < 4096} (records: $B.sized_rope, table: string
    table_len): bool = let
  val () = _mkdir("build/repin-tests")
  val () = _make_file("build/repin-tests/records.tsv", "", 420)
  val @(path_array, path_used) = _text_array("build/repin-tests/records.tsv")
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val written = write_rope_file(path_view, path_used, records)
  var text : $B.builder(0) = $B.create()
  val @(ended, _) = read_file(path_view, path_used, text)
  val @(text_array, text_used) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val rendered = $B.sized_rope_create()
  val bad = render_table(text_view, text_used, rendered)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val same = _rope_is(rendered, table)
in written && bad = 0 && same && (case+ ended of Read_whole() => true | _ => false) end

(* The records of the text rewritten by the releases *)
fn _records_of {text_len,releases_len:nat | text_len < 4096; releases_len < 4096}
  (text: string text_len, releases: string releases_len, now: lint): $B.sized_rope = let
  val @(text_array, text_used) = _text_array(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val @(releases_array, releases_used) = _text_array(releases)
  val @(releases_frozen, releases_view) = $A.freeze<byte>(releases_array)
  val out = $B.sized_rope_create()
  val records = $B.sized_rope_create()
  val _ = rewrite_actions(text_view, text_used, releases_view, releases_used, now, out, records)
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  val () = $A.drop<byte>(releases_frozen, releases_view)
  val () = $A.free<byte>($A.thaw<byte>(releases_frozen))
  val () = discard_rope(out)
in records end

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

(* ============================================================
   The action pins
   ============================================================ *)

(* A pin moves to the newest release of its major that is a candidate *)
fn test_actions_pin_moved_to_a_minor_of_the_same_major (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n", true)

(* The newest release is 6 days old and is not the target: the one before it, 8 days old, is *)
fn test_actions_newest_six_days_old_the_one_before_eight_days_is_the_target (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1792108800\n\
actions/checkout v4.6.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1792281600\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t8\tmoved\n", true)

(* A pin at the 8 day old target, with a 6 day old release above it, is too new and is left *)
fn test_actions_pin_at_the_target_with_a_younger_release_is_too_new (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1792108800\n\
actions/checkout v4.6.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1792281600\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.5.0\tv4.6.0\t6\ttoo new\n", false)

(* A release exactly 7 days old is a candidate *)
fn test_actions_release_exactly_seven_days_old_is_moved_to (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1792195200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t7\tmoved\n", true)

(* A release 6 days 23 hours 59 minutes 59 seconds old is not a candidate *)
fn test_actions_release_one_second_short_of_seven_days_is_too_new (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1792195201\n",
    _now(),
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t6\ttoo new\n", false)

(* A newer major version is not moved *)
fn test_actions_new_major_is_not_moved (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n\
actions/checkout v5.0.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1791763200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.5.0\tv5.0.0\t12\tmajor, not moved\n", false)

(* A minor of the same major moves although a newer major exists *)
fn test_actions_minor_still_moves_when_a_major_exists (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n\
actions/checkout v5.0.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1791763200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n", true)

(* A pin at the newest release is current *)
fn test_actions_current_pin_is_left (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1792713600\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.5.0\tv4.5.0\t1\tcurrent\n", false)

(* A bats-lang pin is left alone, in any spelling, with no record *)
fn test_actions_bats_lang_pin_is_left_alone (): bool =
  _rewrite_is(
    "      - uses: bats-lang/bats/.github/actions/setup@\
11d5960a326750d5838078e36cf38b85af677262 # bats main, PR #287\n\
      - uses: \"bats-lang/bats@11d5960a326750d5838078e36cf38b85af677262\"\n",
    "bats-lang/bats v9.9.9 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1790208000\n",
    _now(),
    "      - uses: bats-lang/bats/.github/actions/setup@\
11d5960a326750d5838078e36cf38b85af677262 # bats main, PR #287\n\
      - uses: \"bats-lang/bats@11d5960a326750d5838078e36cf38b85af677262\"\n",
    "", false)

(* A release whose tag is annotated: the releases text holds the commit, and the pin takes it *)
fn test_actions_annotated_tag_uses_the_commit_of_the_releases_text (): bool =
  _rewrite_is(
    "      - uses: github/codeql-action/init@11d5960a326750d5838078e36cf38b85af677262 # v3.1.0\n",
    "github/codeql-action v3.1.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
github/codeql-action v3.2.0 cccccccccccccccccccccccccccccccccccccccc 1791763200\n",
    _now(),
    "      - uses: github/codeql-action/init@cccccccccccccccccccccccccccccccccccccccc # v3.2.0\n",
    "action\tgithub/codeql-action/init\tv3.1.0\tv3.2.0\t12\tmoved\n", true)

(* The comment is replaced by the release, never doubled, and the second run changes nothing *)
fn test_actions_comment_is_replaced_never_doubled (): bool =
  _rewrite_is(
    "      -   uses:   actions/checkout@11d5960a326750d5838078e36cf38b85af677262   # v4.4.0   \n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      -   uses:   actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n", true)
  && _rewrite_is(
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.5.0\tv4.5.0\t12\tcurrent\n", false)

(* The lines between the pin-rewrite markers are copied as they are, in any spelling *)
fn test_actions_lines_between_the_markers_are_untouched (): bool =
  _rewrite_is(
    "# pin-rewrite begin\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n\
      - uses: \"actions/checkout@11d5960a326750d5838078e36cf38b85af677262\"\n\
# pin-rewrite end\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "# pin-rewrite begin\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n\
      - uses: \"actions/checkout@11d5960a326750d5838078e36cf38b85af677262\"\n\
# pin-rewrite end\n\
      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n", true)

(* A last line without a newline stays without one *)
fn test_actions_text_without_final_newline_keeps_it_that_way (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0",
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n", true)

(* A pin above every release is current, never moved down *)
fn test_actions_pin_is_never_moved_to_a_lower_version (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb # v4.6.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      - uses: actions/checkout@bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb # v4.6.0\n",
    "action\tactions/checkout\tv4.6.0\tv4.6.0\t0\tcurrent\n", false)

(* A tag that is not a version tag (a prerelease) is never the target *)
fn test_actions_prerelease_tag_is_never_the_target (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0-rc1 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n",
    _now(),
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.4.0\t30\tcurrent\n", false)

(* v4.10.0 is above v4.9.0 *)
fn test_actions_the_higher_number_wins_not_the_longer_text (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.9.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1790208000\n\
actions/checkout v4.10.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1790208000\n\
actions/checkout v4.9.1 cccccccccccccccccccccccccccccccccccccccc 1790208000\n",
    _now(),
    "      - uses: actions/checkout@bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb # v4.10.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.10.0\t30\tmoved\n", true)

(* A repository with no release in the text is current *)
fn test_actions_repository_with_no_release_is_current (): bool =
  _rewrite_is(
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "actions/cache v3.0.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1790208000\n",
    _now(),
    "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n",
    "action\tactions/checkout\tv4.4.0\tv4.4.0\t0\tcurrent\n", false)

(* A line that holds a pin in another spelling is refused, named by its number: quoted double,
    quoted single, flow, text after the token, no comment, no space after the hash, text after the
    tag, comment is not a version, commented out, carriage return, other key, hash against the
    pin, no space after the dash, empty part *)
fn test_actions_every_other_spelling_of_a_pin_line_is_refused (): bool =
  let
    val rel = "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n"
  in
  _refused_line("jobs:\n\
      - uses: \"actions/checkout@11d5960a326750d5838078e36cf38b85af677262\" # v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: 'actions/checkout@11d5960a326750d5838078e36cf38b85af677262' # v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - {uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262}\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 extra # v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 #v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0 note\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # main\n", rel) = 2
  && _refused_line("jobs:\n\
      # uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\r\n", rel) = 2
  && _refused_line("jobs:\n\
      - name: x uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 #
          v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262# v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      -uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n", rel) = 2
  && _refused_line("jobs:\n\
      - uses: actions//checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n", rel) = 2
  end

(* A releases text is lines of `owner/repo tag commit seconds` and nothing else *)
fn test_actions_releases_lines_are_validated (): bool =
  _bad_release("") = 0
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 0
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5") = 0
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n\
a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 0
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n\
bad\n") = 2
  && _bad_release("a/b v1 AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA 5\n") = 1
  && _bad_release("a/b v1 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 5\n") = 1
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5x\n") = 1
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 1234567890123\n") = 1
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n\
\n\
a/b v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 2
  && _bad_release("a/b/c v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 1
  && _bad_release("a/b v1 11d5960a326750d5838078e36cf38b85af677262 5 6\n") = 1
  && _bad_release("a/b  v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 1
  && _bad_release("ab v1 11d5960a326750d5838078e36cf38b85af677262 5\n") = 1

(* A version tag is an optional v and one to eight numbers of one to nine digits *)
fn test_actions_version_tags (): bool =
  _version_ok("v4") && _version_ok("4.4.0") && _version_ok("v4.4.0") && _version_ok("v1.2.3.4")
  && _version_ok("v123456789.0") && ~_version_ok("") && ~_version_ok("v") && ~_version_ok("v4.")
  && ~_version_ok("v4..1") && ~_version_ok("v4.5.0-rc1") && ~_version_ok("v1234567890")
  && ~_version_ok("vv4") && ~_version_ok("main") && ~_version_ok("v1.2.3.4.5.6.7.8.9")
  && _version_ok("v1.2.3.4.5.6.7.8")

(* Versions compare number by number, a missing number being 0 *)
fn test_actions_versions_compare_by_number (): bool =
  _version_compare("v4.4.0", "v4.5.0") = ~1 && _version_compare("v4.5.0", "v4.4.0") = 1
  && _version_compare("4.4.0", "v4.4.0") = 0 && _version_compare("v4", "v4.0.0") = 0
  && _version_compare("v4.10.0", "v4.9.9") = 1 && _version_compare("v1.2.3.4", "v1.2.3") = 1
  && _version_compare("v1.2.3", "v1.2.3.4") = ~1 && _version_compare("v1.2.3.0", "v1.2.3") = 0
  && _version_compare("v5", "v4.99.99") = 1

(* The records of one row of each status, written to a file and read back as `repin table`
   reads them, are the table of #410 byte for byte *)
fn test_actions_records_are_the_table (): bool =
  _records_table_is(
    _records_of(
      "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n\
      - uses: actions/setup-node@dddddddddddddddddddddddddddddddddddddddd # v4.0.0\n\
      - uses: actions/cache@eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee # v3.1.0\n\
      - uses: actions/upload-artifact@cccccccccccccccccccccccccccccccccccccccc # v4.1.0\n",
      "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n\
actions/setup-node v4.0.0 dddddddddddddddddddddddddddddddddddddddd 1790208000\n\
actions/setup-node v5.0.0 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb 1790208000\n\
actions/cache v3.1.0 eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee 1790208000\n\
actions/cache v3.2.0 ffffffffffffffffffffffffffffffffffffffff 1792540800\n\
actions/upload-artifact v4.1.0 cccccccccccccccccccccccccccccccccccccccc 1792713600\n",
      _now()),
    "| Kind | Name | Old | New | Release age | Status |\n\
| --- | --- | --- | --- | --- | --- |\n\
| action | actions/checkout | v4.4.0 | v4.5.0 | 12 days | moved |\n\
| action | actions/setup-node | v4.0.0 | v5.0.0 | 30 days | major, not moved |\n\
| action | actions/cache | v3.1.0 | v3.2.0 | 3 days | too new |\n\
| action | actions/upload-artifact | v4.1.0 | v4.1.0 | 1 day | current |\n")

(* A directory with one refused file writes no file at all, not even the one that moves *)
fn test_actions_a_refused_file_leaves_every_file_as_it_was (): bool = let
  val () = _mkdir("build/repin-tests")
  val () = _mkdir("build/repin-tests/refused")
  val () = _mkdir("build/repin-tests/refused/workflows")
  val moving = "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n"
  val refused =
      "      - uses: \"actions/checkout@11d5960a326750d5838078e36cf38b85af677262\" # v4.4.0\n"
  val () = _make_file("build/repin-tests/refused/workflows/a.yml", moving, 420)
  val () = _make_file("build/repin-tests/refused/workflows/b.yml", refused, 420)
  val () = _make_file("build/repin-tests/refused/releases.txt",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n", 420)
  val @(status, records) = _run("build/repin-tests/refused/workflows",
      "build/repin-tests/refused/releases.txt", _now())
  val () = discard_rope(records)
in
  status = 1 && _file_is("build/repin-tests/refused/workflows/a.yml", moving)
  && _file_is("build/repin-tests/refused/workflows/b.yml", refused)
end

(* The files .yml and .yaml are rewritten in place with their permission bits, the others
   are not read, and the records come in the order of the file names *)
fn test_actions_files_are_rewritten_in_place (): bool = let
  val () = _mkdir("build/repin-tests")
  val () = _mkdir("build/repin-tests/moved")
  val () = _mkdir("build/repin-tests/moved/workflows")
  val moving = "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n"
  val current = "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n"
  val () = _make_file("build/repin-tests/moved/workflows/a.yml", moving, 493)
  val () = _make_file("build/repin-tests/moved/workflows/b.yml", current, 420)
  val () = _make_file("build/repin-tests/moved/workflows/c.yaml", moving, 420)
  val () = _make_file("build/repin-tests/moved/workflows/notes.txt", moving, 420)
  val () = _make_file("build/repin-tests/moved/releases.txt",
    "actions/checkout v4.4.0 11d5960a326750d5838078e36cf38b85af677262 1790208000\n\
actions/checkout v4.5.0 aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 1791763200\n", 420)
  val @(status, records) = _run("build/repin-tests/moved/workflows",
      "build/repin-tests/moved/releases.txt", _now())
  val records_ok = _rope_is(records,
    "action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n\
action\tactions/checkout\tv4.5.0\tv4.5.0\t12\tcurrent\n\
action\tactions/checkout\tv4.4.0\tv4.5.0\t12\tmoved\n")
in
  status = 0 && records_ok && _file_is("build/repin-tests/moved/workflows/a.yml",
      "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n")
  && _mode_of("build/repin-tests/moved/workflows/a.yml") = 493
  && _file_is("build/repin-tests/moved/workflows/b.yml", current)
  && _file_is("build/repin-tests/moved/workflows/c.yaml",
      "      - uses: actions/checkout@aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa # v4.5.0\n")
  && _file_is("build/repin-tests/moved/workflows/notes.txt", moving)
end

(* A releases file with a line that is not a release writes nothing *)
fn test_actions_bad_releases_file_writes_nothing (): bool = let
  val () = _mkdir("build/repin-tests")
  val () = _mkdir("build/repin-tests/bad-releases")
  val () = _mkdir("build/repin-tests/bad-releases/workflows")
  val moving = "      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4.4.0\n"
  val () = _make_file("build/repin-tests/bad-releases/workflows/a.yml", moving, 420)
  val () = _make_file("build/repin-tests/bad-releases/releases.txt", "actions/checkout v4.5.0\n",
      420)
  val @(status, records) = _run("build/repin-tests/bad-releases/workflows",
      "build/repin-tests/bad-releases/releases.txt", _now())
  val () = discard_rope(records)
in status = 1 && _file_is("build/repin-tests/bad-releases/workflows/a.yml", moving) end

(* A directory or a releases file that is not there is a failure *)
fn test_actions_missing_directory_and_missing_releases_fail (): bool = let
  val () = _mkdir("build/repin-tests")
  val () = _mkdir("build/repin-tests/missing")
  val () = _make_file("build/repin-tests/missing/releases.txt", "", 420)
  val @(no_directory, records) = _run("build/repin-tests/missing/nowhere",
      "build/repin-tests/missing/releases.txt", _now())
  val () = discard_rope(records)
  val () = _mkdir("build/repin-tests/missing/workflows")
  val @(no_releases, records2) = _run("build/repin-tests/missing/workflows",
      "build/repin-tests/missing/absent.txt", _now())
  val () = discard_rope(records2)
in no_directory = 1 && no_releases = 1 end

end
