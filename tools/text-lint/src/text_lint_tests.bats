(* text_lint_tests -- the tests of text-lint (bats-lang/repository-prototype#487), run by
   `bats test` in tools/text-lint. Each check of the lint has a fixture body in tests/bodies
   (a pull request body as a file) and the cases below name the findings the lint gives it,
   word for word; the event cases run lint_event on the files of tests/events. The head is
   the constant _head () in every case. Keyword: text-lint tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "event.sats"
staload "gated.sats"
staload "lint.sats"
staload "support.sats"

fn _test_phrases (): string 29 = "tests/bodies/test-phrases.txt"

fn _head (): string 40 = "0123456789abcdef0123456789abcdef01234567"

fn text_length {text_len:nat} (text: string text_len): int text_len = g1u2i(string1_length(text))

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
   literal_len: int literal_len, at: int at): bool =
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

fn _rope_is {literal_len:nat} (text: $B.sized_rope, literal: string literal_len): bool =
  _chunks_are($B.sized_rope_chunks(text), literal, text_length(literal), 0)

(* The file at the path read whole: the array, its length, whether it was read *)
fn _file {path_len:nat | path_len < 200} (path: string path_len)
  : @(bool, [m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) = let
  var path_builder : $B.builder(0) = $B.create()
  val () = $B.bput(path_builder, path)
  val @(path_array, path_len2) = $B.to_arr(path_builder)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var text : $B.builder(0) = $B.create()
  val @(ended, _) = read_file(path_view, path_len2, text)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val @(array, used) = $B.to_arr(text)
in
  case+ ended of
  | Read_whole() => @(true, array, used)
  | _ => @(false, array, 0)
end

fn _text {text_len:nat | text_len < 4096} (text: string text_len)
  : @([m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) = let
  var builder : $B.builder(0) = $B.create()
  val () = $B.bput(builder, text)
in $B.to_arr(builder) end

(* Whether the lint of the body in the file (head the constant, phrases the file
   tests/bodies/phrases.txt when phrases) gives that many findings and that text *)
fn _fixture_is {path_len,head_len0,phrases_path_len,expected_len:nat | path_len < 200; head_len0 < 4096; phrases_path_len < 200}
  (path: string path_len, head: string head_len0, phrases_path: string phrases_path_len, count: int, expected: string expected_len)
  : bool = let
  val @(body_ok, body_array, body_len) = _file(path)
  val @(phrases_ok, phrases_array, phrases_len) = _file(phrases_path)
  val @(head_array, head_len) = _text(head)
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  val out = $B.sized_rope_create()
  val found = lint_body(body_view, body_len, head_view, head_len, phrases_view, phrases_len, out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  val same = _rope_is(out, expected)
in body_ok && found = count && same end

(* The same for a body in memory *)
fn _body_is {body_len,expected_len:nat | body_len < 4096}
  (body: string body_len, count: int, expected: string expected_len): bool = let
  val @(body_array, used) = _text(body)
  val @(phrases_array, phrases_used) = _text("")
  val @(head_array, head_len) = _text(_head())
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  val out = $B.sized_rope_create()
  val found = lint_body(body_view, used, head_view, head_len, phrases_view, phrases_used, out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  val same = _rope_is(out, expected)
in found = count && same end

(* The status and the findings lint_event gives the event file *)
fn _event_full {path_len,changes_len0,findings_len,status_len:nat | path_len < 200; changes_len0 < 200}
  (path: string path_len, changes_path: string changes_len0, code: int,
   findings_text: string findings_len, status_text: string status_len): bool = let
  val @(event_ok, event_array, event_len) = _file(path)
  val @(phrases_array, phrases_len) = _text("")
  val @(url_array, url_len) = _text("https://github.com/o/r/actions/runs/1")
  val @(event_frozen, event_view) = $A.freeze<byte>(event_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(url_frozen, url_view) = $A.freeze<byte>(url_array)
  val findings = $B.sized_rope_create()
  val status = $B.sized_rope_create()
  val @(changes_ok, changes_array, changes_len) = _file(changes_path)
  val @(triggers_ok, triggers_array, triggers_len) = _file("gated-triggers.txt")
  val @(base_array, base_len) = _text("tests/gated/base")
  val @(changes_frozen, changes_view) = $A.freeze<byte>(changes_array)
  val @(base_frozen, base_view) = $A.freeze<byte>(base_array)
  val @(triggers_frozen, triggers_view) = $A.freeze<byte>(triggers_array)
  val got = lint_event(event_view, event_len, phrases_view, phrases_len, url_view, url_len,
    changes_view, changes_len, base_view, base_len, triggers_view, triggers_len, findings, status)
  val () = $A.drop<byte>(changes_frozen, changes_view)
  val () = $A.free<byte>($A.thaw<byte>(changes_frozen))
  val () = $A.drop<byte>(base_frozen, base_view)
  val () = $A.free<byte>($A.thaw<byte>(base_frozen))
  val () = $A.drop<byte>(triggers_frozen, triggers_view)
  val () = $A.free<byte>($A.thaw<byte>(triggers_frozen))
  val () = $A.drop<byte>(event_frozen, event_view)
  val () = $A.free<byte>($A.thaw<byte>(event_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(url_frozen, url_view)
  val () = $A.free<byte>($A.thaw<byte>(url_frozen))
  val same_findings = _rope_is(findings, findings_text)
  val same_status = _rope_is(status, status_text)
in event_ok && changes_ok && triggers_ok && got = code && same_findings && same_status end

(* The status and the findings lint_event gives the event file, no workflow changed *)
fn _event_is {path_len,findings_len,status_len:nat | path_len < 200}
  (path: string path_len, code: int, findings_text: string findings_len,
   status_text: string status_len): bool =
  _event_full(path, "tests/gated/changes-empty.diff", code, findings_text, status_text)

(* The findings of the row scratch-run for the event file and the changes file (the base
   checkout is tests/gated/base, the triggers are gated-triggers.txt): the count, and the text *)
fn _gated_is {event_len,changes_len,findings_len:nat | event_len < 200; changes_len < 200}
  (event_path: string event_len, changes_path: string changes_len, count: int,
   findings_text: string findings_len): bool = let
  val @(event_ok, event_array, event_used) = _file(event_path)
  val @(changes_ok, changes_array, changes_used) = _file(changes_path)
  val @(triggers_ok, triggers_array, triggers_used) = _file("gated-triggers.txt")
  val @(base_array, base_used) = _text("tests/gated/base")
  val @(event_frozen, event_view) = $A.freeze<byte>(event_array)
  val @(changes_frozen, changes_view) = $A.freeze<byte>(changes_array)
  val @(triggers_frozen, triggers_view) = $A.freeze<byte>(triggers_array)
  val @(base_frozen, base_view) = $A.freeze<byte>(base_array)
  val out = $B.sized_rope_create()
  val found = lint_gated(event_view, event_used, changes_view, changes_used, base_view, base_used,
    triggers_view, triggers_used, out)
  val () = $A.drop<byte>(event_frozen, event_view)
  val () = $A.free<byte>($A.thaw<byte>(event_frozen))
  val () = $A.drop<byte>(changes_frozen, changes_view)
  val () = $A.free<byte>($A.thaw<byte>(changes_frozen))
  val () = $A.drop<byte>(triggers_frozen, triggers_view)
  val () = $A.free<byte>($A.thaw<byte>(triggers_frozen))
  val () = $A.drop<byte>(base_frozen, base_view)
  val () = $A.free<byte>($A.thaw<byte>(base_frozen))
  val same = _rope_is(out, findings_text)
in event_ok && changes_ok && triggers_ok && found = count && same end

fn _exempt_is {ref_len,login_len:nat | ref_len < 4096; login_len < 4096}
  (ref: string ref_len, login: string login_len): bool = let
  val @(ref_array, ref_used) = _text(ref)
  val @(login_array, login_used) = _text(login)
  val @(ref_frozen, ref_view) = $A.freeze<byte>(ref_array)
  val @(login_frozen, login_view) = $A.freeze<byte>(login_array)
  val exempt = is_exempt(ref_view, ref_used, login_view, login_used)
  val () = $A.drop<byte>(ref_frozen, ref_view)
  val () = $A.free<byte>($A.thaw<byte>(ref_frozen))
  val () = $A.drop<byte>(login_frozen, login_view)
  val () = $A.free<byte>($A.thaw<byte>(login_frozen))
in exempt end


(* The phrases found in the body by the phrases text (lines of the form of the file) *)
fn _hits {phrases_len,body_len:nat | phrases_len < 4096; body_len < 4096}
  (phrase_text: string phrases_len, body_text: string body_len): int = let
  val @(body_array, used) = _text(body_text)
  val @(phrases_array, phrases_used) = _text(phrase_text)
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val out = $B.sized_rope_create()
  val found = phrase_findings(body_view, used, phrases_view, phrases_used, out)
  val () = discard_rope(out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
in found end

(* The phrases found in the body made of the pieces by the phrases file of the lint *)
fn _real_hits {first_len,second_len:nat | first_len < 4096; second_len < 4096}
  (first: string first_len, second: string second_len): int = let
  var body : $B.builder(0) = $B.create()
  val () = $B.bput(body, first)
  val () = $B.bput(body, second)
  val @(body_array, used) = $B.to_arr(body)
  val @(ok, phrases_array, phrases_used) = _file("phrases.txt")
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val out = $B.sized_rope_create()
  val found = phrase_findings(body_view, used, phrases_view, phrases_used, out)
  val () = discard_rope(out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
in if ok then found else ~1 end

(* Whether the rope starts with the literal *)
fn _rope_starts {literal_len:nat | literal_len <= 4096} (text: $B.sized_rope, literal: string literal_len): bool =
  case+ $B.sized_rope_chunks(text) of
  | ~$B.rope_sized_nil() => false
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val n = text_length(literal)
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val same = (if used >= n then _equal_from(view, n, 0, literal, 0) else false): bool
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
      val () = $B.rope_sized_list_free(rest)
    in same end

(* Whether the lint of the body in the file, with the phrases file of the lint, gives a
   finding and the first starts with the literal *)
fn _fixture_starts {path_len,beginning_len:nat | path_len < 200; beginning_len <= 4096}
  (path: string path_len, beginning: string beginning_len): bool = let
  val @(body_ok, body_array, body_len) = _file(path)
  val @(phrases_ok, phrases_array, phrases_len) = _file("phrases.txt")
  val @(head_array, head_len) = _text(_head())
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  val out = $B.sized_rope_create()
  val found = lint_body(body_view, body_len, head_view, head_len, phrases_view, phrases_len, out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  val prefixed = _rope_starts(out, beginning)
in body_ok && phrases_ok && found >= 1 && prefixed end

(* Whether every phrase line of phrases[0, used) from start finds its own example (a dash is an
   example built in the tests) *)
fun _examples {l:agz}{n:pos | n <= 524288}{used:nat | used <= n}{start:nat | start <= used} .<used - start>.
  (phrases: !$A.borrow(byte, l, n), used: int used, start: int start): bool = let
  val raw = find_byte(phrases, used, start, 10)
  val ok =
    (if raw <= start then true
     else if byte2int0($A.read<byte>(phrases, start)) = 35 then true
     else let
       val t1 = find_byte(phrases, raw, start, 9)
     in
       if t1 >= raw then false
       else let
         val t2 = find_byte(phrases, raw, t1 + 1, 9)
       in
         if t2 >= raw then false
         else let
           val t3 = find_byte(phrases, raw, t2 + 1, 9)
         in
           if t3 >= raw then false
           else if t3 - t2 = 2 && span_is(phrases, t2 + 1, t3, "-") then true
           else let
             var body : $B.builder(0) = $B.create()
             val () = put_range(phrases, t2 + 1, t3, body)
             val @(body_array, body_len) = $B.to_arr(body)
             var one : $B.builder(0) = $B.create()
             val () = put_range(phrases, start, raw, one)
             val @(one_array, one_len) = $B.to_arr(one)
             val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
             val @(one_frozen, one_view) = $A.freeze<byte>(one_array)
             val out = $B.sized_rope_create()
             val found = phrase_findings(body_view, body_len, one_view, one_len, out)
             val () = discard_rope(out)
             val () = $A.drop<byte>(body_frozen, body_view)
             val () = $A.free<byte>($A.thaw<byte>(body_frozen))
             val () = $A.drop<byte>(one_frozen, one_view)
             val () = $A.free<byte>($A.thaw<byte>(one_frozen))
           in found = 1 end
         end
       end
     end): bool
in
  if ~ok then false
  else if raw >= used then true
  else _examples(phrases, used, raw + 1)
end

(* The original rows (keyword: text-lint original). tests/original/phrases.tsv is a copy of the
   phrases of quire's guidelines, corpus.txt has a text on each line that starts with a tag (the
   line of phrases.txt, the original row, and a plus when the text is refused or a minus when it
   passes), and oracle.txt is the output of quire's program on the corpus. *)

(* The end of the digits that start at i *)
fun _digits_end {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i): [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else let
    val c = byte2int0($A.read<byte>(bytes, i))
  in
    if c >= 48 && c <= 57 then _digits_end(bytes, limit, i + 1) else i
  end

(* The number the digits bytes[i, stop) write, added to what was read before them *)
fun _digits_value {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), stop: int stop, i: int i, before: int): int =
  if i >= stop then before
  else _digits_value(bytes, stop, i + 1, before * 10 + (byte2int0($A.read<byte>(bytes, i)) - 48))

(* The tag of the corpus line bytes[start, stop): the line of phrases.txt, the original row and
   the sign (one for a plus, zero for a minus); each is negative when the line has no tag *)
fn _tag {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): @(int, int, int) = let
  val line_end = _digits_end(bytes, stop, start)
in
  if line_end >= stop then @(~1, ~1, ~1)
  else if line_end = start then @(~1, ~1, ~1)
  else if byte2int0($A.read<byte>(bytes, line_end)) != 58 then @(~1, ~1, ~1)
  else let
    val row_end = _digits_end(bytes, stop, line_end + 1)
  in
    if row_end >= stop then @(~1, ~1, ~1)
    else if row_end = line_end + 1 then @(~1, ~1, ~1)
    else let
      val sign_byte = byte2int0($A.read<byte>(bytes, row_end))
      val sign = (if sign_byte = 43 then 1 else if sign_byte = 45 then 0 else ~1): int
    in
      @(_digits_value(bytes, line_end, start, 0), _digits_value(bytes, row_end, line_end + 1, 0), sign)
    end
  end
end

(* Where the text of the corpus line bytes[start, stop) starts, after its tag and a blank *)
fn _text_start {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): [t:nat | start <= t; t <= stop] int t = let
  val line_end = _digits_end(bytes, stop, start)
in
  if line_end >= stop then stop
  else let
    val row_end = _digits_end(bytes, stop, line_end + 1)
  in
    if row_end + 2 <= stop then row_end + 2 else stop
  end
end

(* Whether the oracle's output (lines "text:N: row R: ...") names the line of the corpus
   by its number and, when the row is not negative, with that row *)
fun _oracle_has {l:agz}{n:pos | n <= 524288}{used:nat | used <= n}{start:nat | start <= used} .<used - start>.
  (oracle: !$A.borrow(byte, l, n), used: int used, start: int start, line_number: int, row: int): bool = let
  val raw = find_byte(oracle, used, start, 10)
  val here =
    (if raw - start < 5 then false
     else if ~span_is(oracle, start, start + 5, "text:") then false
     else let
       val number_end = _digits_end(oracle, raw, start + 5)
     in
       if number_end + 6 > raw then false
       else if ~span_is(oracle, number_end, number_end + 6, ": row ") then false
       else if _digits_value(oracle, number_end, start + 5, 0) != line_number then false
       else let
         val row_end = _digits_end(oracle, raw, number_end + 6)
       in
         row < 0 || _digits_value(oracle, row_end, number_end + 6, 0) = row
       end
     end): bool
in
  if here then true
  else if raw >= used then false
  else _oracle_has(oracle, used, raw + 1, line_number, row)
end

(* How many phrases the lint finds in text[start, stop) with the phrases of phrases[from, upto) *)
fn _found_with {tl,pl:agz}{tn,pn:pos | tn <= 524288; pn <= 524288}
  {stop:nat | stop <= tn}{start:nat | start <= stop}{upto:nat | upto <= pn}{from:nat | from <= upto}
  (text: !$A.borrow(byte, tl, tn), start: int start, stop: int stop,
   phrases: !$A.borrow(byte, pl, pn), from: int from, upto: int upto): int = let
  var body : $B.builder(0) = $B.create()
  val () = put_range(text, start, stop, body)
  val @(body_array, body_len) = $B.to_arr(body)
  var one : $B.builder(0) = $B.create()
  val () = put_range(phrases, from, upto, one)
  val @(one_array, one_len) = $B.to_arr(one)
  val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
  val @(one_frozen, one_view) = $A.freeze<byte>(one_array)
  val out = $B.sized_rope_create()
  val found = phrase_findings(body_view, body_len, one_view, one_len, out)
  val () = discard_rope(out)
  val () = $A.drop<byte>(body_frozen, body_view)
  val () = $A.free<byte>($A.thaw<byte>(body_frozen))
  val () = $A.drop<byte>(one_frozen, one_view)
  val () = $A.free<byte>($A.thaw<byte>(one_frozen))
in found end

(* How many lines text[start, used) has that are not empty *)
fun _lines_read {l:agz}{n:pos}{used:nat | used <= n}{start:nat | start <= used} .<used - start>.
  (text: !$A.borrow(byte, l, n), used: int used, start: int start): int =
  if start >= used then 0
  else let
    val raw = find_byte(text, used, start, 10)
    val here = (if raw > start then 1 else 0): int
  in
    if raw >= used then here else here + _lines_read(text, used, raw + 1)
  end

(* How many lines of the copy of the original phrases are of the text kind *)
fun _rows_read {l:agz}{n:pos}{used:nat | used <= n}{start:nat | start <= used} .<used - start>.
  (tsv: !$A.borrow(byte, l, n), used: int used, start: int start): int =
  if start >= used then 0
  else let
    val raw = find_byte(tsv, used, start, 10)
    val here = (if raw - start >= 5 then (if span_is(tsv, start, start + 5, "text\t") then 1 else 0) else 0): int
  in
    if raw >= used then here else here + _rows_read(tsv, used, raw + 1)
  end

(* The plus lines of the corpus that carry the line of phrases.txt phrases_line: how many, or
   negative when one is not found by that line alone, not named by the oracle with its row, or
   of another row than the first; a miss is said *)
fun _plus_lines {cl,pl,ol:agz}{cn,pn,on:pos | cn <= 524288; pn <= 524288; on <= 524288}
  {cused:nat | cused <= cn}{start:nat | start <= cused}{oused:nat | oused <= on}
  {upto:nat | upto <= pn}{from:nat | from <= upto} .<cused - start>.
  (corpus: !$A.borrow(byte, cl, cn), cused: int cused, start: int start, line_number: int,
   phrases: !$A.borrow(byte, pl, pn), from: int from, upto: int upto, phrases_line: int,
   oracle: !$A.borrow(byte, ol, on), oused: int oused, row: int, count: int): int = let
  val raw = find_byte(corpus, cused, start, 10)
  val @(tag_line, tag_row, tag_sign) = _tag(corpus, start, raw)
  val relevant = (tag_line = phrases_line && tag_sign = 1): bool
  val found = (if relevant then _found_with(corpus, start, raw, phrases, from, upto) else 1): int
  val named = (if relevant then _oracle_has(oracle, oused, 0, line_number, tag_row) else true): bool
  val same_row = (~relevant || row < 0 || row = tag_row): bool
  val count2 = (if relevant then count + 1 else count): int
  val row2 = (if relevant && row < 0 then tag_row else row): int
in
  if found < 1 then let
    val () = println! ("miss: corpus line ", line_number, " is not found by line ", phrases_line, " of phrases.txt alone")
  in ~1 end
  else if ~named then let
    val () = println! ("miss: corpus line ", line_number, " is not named by the oracle with row ", tag_row)
  in ~1 end
  else if ~same_row then let
    val () = println! ("miss: corpus line ", line_number, " carries another row than the first plus line of line ", phrases_line)
  in ~1 end
  else if raw >= cused then count2
  else _plus_lines(corpus, cused, raw + 1, line_number + 1, phrases, from, upto, phrases_line,
    oracle, oused, row2, count2)
end

(* (a) How many lines of phrases.txt (from start) have a plus line, found by that line alone,
   named by the oracle with the line's row, all of one row *)
fun _reach_phrases {cl,pl,ol:agz}{cn,pn,on:pos | cn <= 524288; pn <= 524288; on <= 524288}
  {cused:nat | cused <= cn}{pused:nat | pused <= pn}{start:nat | start <= pused}{oused:nat | oused <= on}
  .<pused - start>.
  (corpus: !$A.borrow(byte, cl, cn), cused: int cused,
   phrases: !$A.borrow(byte, pl, pn), pused: int pused, start: int start, phrases_line: int,
   oracle: !$A.borrow(byte, ol, on), oused: int oused): int =
  if start >= pused then 0
  else let
    val raw = find_byte(phrases, pused, start, 10)
    val is_phrase = (if raw > start then byte2int0($A.read<byte>(phrases, start)) != 35 else false): bool
    val here =
      (if ~is_phrase then 0
       else let
         val count = _plus_lines(corpus, cused, 0, 1, phrases, start, raw, phrases_line, oracle, oused, ~1, 0)
       in
         if count >= 1 then 1
         else let
           val () = (if count = 0 then println! ("miss: line ", phrases_line, " of phrases.txt has no plus line in the corpus") else ())
         in 0 end
       end): int
  in
    if raw >= pused then here
    else here + _reach_phrases(corpus, cused, phrases, pused, raw + 1, phrases_line + 1, oracle, oused)
  end

(* (b) How many lines of the corpus (from start) are found by the lint just when the oracle names
   them, with the sign of the tag a plus just then *)
fun _reach_corpus {cl,pl,ol:agz}{cn,pn,on:pos | cn <= 524288; pn <= 524288; on <= 524288}
  {cused:nat | cused <= cn}{start:nat | start <= cused}{pused:nat | pused <= pn}{oused:nat | oused <= on}
  .<cused - start>.
  (corpus: !$A.borrow(byte, cl, cn), cused: int cused, start: int start, line_number: int,
   phrases: !$A.borrow(byte, pl, pn), pused: int pused,
   oracle: !$A.borrow(byte, ol, on), oused: int oused): int =
  if start >= cused then 0
  else let
    val raw = find_byte(corpus, cused, start, 10)
    val @(tag_line, tag_row, tag_sign) = _tag(corpus, start, raw)
    val found = _found_with(corpus, start, raw, phrases, 0, pused)
    val named = _oracle_has(oracle, oused, 0, line_number, ~1)
    val agree = (if named then (found >= 1 && tag_sign = 1) else (found <= 0 && tag_sign = 0)): bool
    val here =
      (if raw = start then 0
       else if agree then 1
       else let
         val named_flag = (if named then 1 else 0): int
         val () = println! ("miss: corpus line ", line_number, " is found ", found, " times by the lint, is named by the oracle ", named_flag, ", sign ", tag_sign)
       in 0 end): int
  in
    if raw >= cused then here
    else here + _reach_corpus(corpus, cused, raw + 1, line_number + 1, phrases, pused, oracle, oused)
  end

(* Whether the corpus (from start) has a line of the row with the sign; with a text span, a plus
   line of the row whose text is that span of the copy *)
fun _corpus_has {cl,tl:agz}{cn,tn:pos | cn <= 524288; tn <= 524288}
  {cused:nat | cused <= cn}{start:nat | start <= cused}{ex_stop:nat | ex_stop <= tn}{ex_start:nat | ex_start <= ex_stop}
  .<cused - start>.
  (corpus: !$A.borrow(byte, cl, cn), cused: int cused, start: int start, row: int, sign: int,
   tsv: !$A.borrow(byte, tl, tn), ex_start: int ex_start, ex_stop: int ex_stop, with_text: bool): bool = let
  val raw = find_byte(corpus, cused, start, 10)
  val @(tag_line, tag_row, tag_sign) = _tag(corpus, start, raw)
  val here =
    (if tag_row != row || tag_sign != sign then false
     else if ~with_text then true
     else spans_equal(corpus, _text_start(corpus, start, raw), raw, tsv, ex_start, ex_stop)): bool
in
  if here then true
  else if raw >= cused then false
  else _corpus_has(corpus, cused, raw + 1, row, sign, tsv, ex_start, ex_stop, with_text)
end

(* (c) How many text rows of the copy (from start) have a plus line and a minus line in the
   corpus, and their example as a plus line of the corpus tagged with the row *)
fun _reach_rows {cl,tl:agz}{cn,tn:pos | cn <= 524288; tn <= 524288}
  {cused:nat | cused <= cn}{tused:nat | tused <= tn}{start:nat | start <= tused} .<tused - start>.
  (corpus: !$A.borrow(byte, cl, cn), cused: int cused,
   tsv: !$A.borrow(byte, tl, tn), tused: int tused, start: int start): int =
  if start >= tused then 0
  else let
    val raw = find_byte(tsv, tused, start, 10)
    val here =
      (if raw - start < 5 then 0
       else if ~span_is(tsv, start, start + 5, "text\t") then 0
       else let
         val row_start = start + 5
         val row_end = find_byte(tsv, raw, row_start, 9)
       in
         if row_end >= raw then 0
         else let
           val regex_end = find_byte(tsv, raw, row_end + 1, 9)
         in
           if regex_end >= raw then 0
           else let
             val example_end = find_byte(tsv, raw, regex_end + 1, 9)
           in
             if example_end >= raw then 0
             else let
               val row = _digits_value(tsv, row_end, row_start, 0)
               val plus = _corpus_has(corpus, cused, 0, row, 1, tsv, 0, 0, false)
               val minus = _corpus_has(corpus, cused, 0, row, 0, tsv, 0, 0, false)
               val example = _corpus_has(corpus, cused, 0, row, 1, tsv, regex_end + 1, example_end, true)
             in
               if plus && minus && example then 1
               else let
                 val () = println! ("miss: row ", row, " of the copy lacks a plus line, a minus line or its example as a plus line")
               in 0 end
             end
           end
         end
       end): int
  in
    if raw >= tused then here
    else here + _reach_rows(corpus, cused, tsv, tused, raw + 1)
  end

(* How many lines of phrases.txt (from start) are phrases: not empty and not a comment *)
fun _phrases_read {l:agz}{n:pos}{used:nat | used <= n}{start:nat | start <= used} .<used - start>.
  (phrases: !$A.borrow(byte, l, n), used: int used, start: int start): int =
  if start >= used then 0
  else let
    val raw = find_byte(phrases, used, start, 10)
    val here = (if raw > start then (if byte2int0($A.read<byte>(phrases, start)) != 35 then 1 else 0) else 0): int
  in
    if raw >= used then here else here + _phrases_read(phrases, used, raw + 1)
  end

$UNITTEST.run begin

(* the bodies that pass: no finding *)
fn test_passing_bodies_have_no_finding (): bool =
  _fixture_is("tests/bodies/pass-fixes.md", _head(), _test_phrases(), 0, "")
  && _fixture_is("tests/bodies/pass-fixes-other-repository.md", _head(), _test_phrases(), 0, "")
  && _fixture_is("tests/bodies/pass-robot-footer.md", _head(), _test_phrases(), 0, "")
  && _fixture_is("tests/bodies/pass-crlf.md", _head(), _test_phrases(), 0, "")

(* first-line: Refs for Fixes, in either spelling of the ticket *)
fn test_refs_instead_of_fixes_is_refused (): bool =
  _fixture_is("tests/bodies/fail-refs.md", _head(), _test_phrases(), 1,
    "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\n")
  && _fixture_is("tests/bodies/fail-refs-other-repository.md", _head(), _test_phrases(), 1,
    "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\n")

(* one-ticket: a second ticket *)
fn test_two_tickets_are_refused (): bool =
  _fixture_is("tests/bodies/fail-two-tickets.md", _head(), _test_phrases(), 1,
    "PR body: Fixes names more than one ticket; one ticket, one PR, and a dependency is its own ticket and PR (one-ticket)\n")

(* head: no Head line, and a Head line that is not the head *)
fn test_head_line_is_there_and_is_the_head (): bool =
  _fixture_is("tests/bodies/fail-no-head.md", _head(), _test_phrases(), 1,
    "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\n")
  && _fixture_is("tests/bodies/fail-head-differs.md", _head(), _test_phrases(), 1,
    "PR body: it describes head fedcba9876543210fedcba9876543210fedcba98 but the head is 0123456789abcdef0123456789abcdef01234567; rewrite the body for the head (head)\n")
  && _fixture_is("tests/bodies/pass-fixes.md", "fedcba9876543210fedcba9876543210fedcba98", _test_phrases(), 1,
    "PR body: it describes head 0123456789abcdef0123456789abcdef01234567 but the head is fedcba9876543210fedcba9876543210fedcba98; rewrite the body for the head (head)\n")

(* evidence: the Evidence heading and a block of a command with its output *)
fn test_evidence_has_a_heading_and_a_command_block (): bool =
  _fixture_is("tests/bodies/fail-no-evidence.md", _head(), _test_phrases(), 1,
    "PR body: no Evidence heading; every claim has its command and raw output (evidence)\n")
  && _fixture_is("tests/bodies/fail-no-command-block.md", _head(), _test_phrases(), 1,
    "PR body: no fenced block that starts with $ <command> and holds its raw output (evidence)\n")

(* footer: the footer *)
fn test_footer_is_the_one_of_the_template (): bool =
  _fixture_is("tests/bodies/fail-wrong-footer.md", _head(), _test_phrases(), 1,
    "PR body: it does not end with the generated-by footer of the template (footer)\n")
  && _fixture_is("tests/bodies/fail-session-url.md", _head(), _test_phrases(), 2,
    "PR body: it does not end with the generated-by footer of the template (footer)\nPR body: it holds a session URL; the footer is the generated-by line alone (footer)\n")
  && _fixture_is("tests/bodies/fail-two-footers.md", _head(), _test_phrases(), 1,
    "PR body: it holds more than one generated-by footer; exactly one (footer)\n")

(* phrases: a phrase of a phrases file is refused with its place, label and reason, a body
   without it passes, and a line of another form is a finding of its own *)
fn test_phrases_of_the_file_are_refused (): bool =
  _fixture_is("tests/bodies/fail-phrase.md", _head(), _test_phrases(), 1,
    "PR body:12: example: a refused phrase (tools/text-lint/phrases.txt line 2): Do not write it.\n")
  && _fixture_is("tests/bodies/fail-phrase.md", _head(), "tests/bodies/none.txt", 0, "")
  && _fixture_is("tests/bodies/pass-fixes.md", _head(), "phrases.txt", 0, "")
  && (_hits("a\tb\n", "b") = 1)
  && (_hits("# a comment\n\n", "b") = 0)

(* phrases: the patterns of the phrases that were regular expressions, each kind with its fixture
   body, found at the line of the body they are on, with the label of the file's line *)
fn test_regular_expression_phrases_have_fixtures (): bool =
  _fixture_starts("tests/bodies/fail-phrase-narrowing.md", "PR body:5: narrowing: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-refs.md", "PR body:5: refs: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-half-done.md", "PR body:5: half-done: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-rerun.md", "PR body:5: rerun: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-unverified.md", "PR body:5: unverified: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-waiting.md", "PR body:5: waiting: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-alternative.md", "PR body:5: alternative: a refused phrase")
  && _fixture_starts("tests/bodies/fail-phrase-waiting-go.md", "PR body:5: waiting-go: a refused phrase")

(* phrases: the example of every line of the phrases file is found by that line alone *)
fn test_every_example_is_found_by_its_line (): bool = let
  val @(ok, array, used) = _file("phrases.txt")
  val @(frozen, view) = $A.freeze<byte>(array)
  val every = ok && _examples(view, used, 0)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in every end

(* phrases: the pattern language: the word edge, the quantifiers, the classes, the backtracking,
   the case *)
fn test_pattern_language (): bool =
  (_hits("l\t\\bfrank\\b\te\tr\n", "a frank man") = 1)
  && (_hits("l\t\\bfrank\\b\te\tr\n", "frankfurt") = 0)
  && (_hits("l\thonest\te\tr\n", "so dishonest") = 1)
  && (_hits("l\thonest\te\tr\n", "HONEST") = 1)
  && (_hits("l\ta?b\te\tr\n", "b") = 1)
  && (_hits("l\tab+c\te\tr\n", "abbbc") = 1)
  && (_hits("l\tab+c\te\tr\n", "ac") = 0)
  && (_hits("l\tab*c\te\tr\n", "ac") = 1)
  && (_hits("l\tx[ab]y\te\tr\n", "xay") = 1)
  && (_hits("l\tx[ab]y\te\tr\n", "xcy") = 0)
  && (_hits("l\tx[^ab]y\te\tr\n", "xcy") = 1)
  && (_hits("l\tx[^ab]y\te\tr\n", "xay") = 0)
  && (_hits("l\tx[^>\\s]*y\te\tr\n", "xaby") = 1)
  && (_hits("l\tx[^>\\s]*y\te\tr\n", "x>y") = 0)
  && (_hits("l\tx\\sy\te\tr\n", "x y") = 1)
  && (_hits("l\t\\d+x\te\tr\n", "12x") = 1)
  && (_hits("l\ta+ab\te\tr\n", "aaab") = 1)
  && (_hits("l\tgo\"?\\b\te\tr\n", "the \"go\"") = 1)
  && (_hits("l\ta.c\te\tr\n", "a.c") = 1)
  && (_hits("l\ta\\.c\te\tr\n", "abc") = 0)

(* phrases: some patterns spell a letter as a class; the words are built here from pieces *)
fn test_class_spelled_patterns (): bool =
  (_real_hits("it is par", "tly done") = 1)
  && (_real_hits("par", "tially done") = 1)
  && (_real_hits("a ", "party") = 0)

(* an empty body fails every check but one-ticket *)
fn test_empty_body_fails_each_row (): bool =
  _fixture_is("tests/bodies/fail-empty.md", _head(), _test_phrases(), 4,
    "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* the edges of first-line: blank lines before, any case, the word edge, the digits *)
fn test_first_line_edges (): bool =
  _body_is("\n\nFixes #1\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("fixes #12\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes #\n", 4, "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fix #1\n", 4, "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* one-ticket: the same ticket named again, in either case, is one ticket; Refixes is not Fixes *)
fn test_same_ticket_twice_is_one_ticket (): bool =
  _body_is("Fixes #1\nand fixes #1 again, and Refixes #2\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes a/b#1\nFixes A/B#1\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes a/b#1\nFixes a/b#2\n", 4, "PR body: Fixes names more than one ticket; one ticket, one PR, and a dependency is its own ticket and PR (one-ticket)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* head: a longer run of digits is not a head; trailing blanks are fine; the last Head line counts *)
fn test_head_line_edges (): bool =
  _body_is("Fixes #1\nHead: 0123456789abcdef0123456789abcdef012345670\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes #1\nHead: 0123456789abcdef0123456789abcdef01234567   \n", 2, "PR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes #1\nHead: fedcba9876543210fedcba9876543210fedcba98\nHead: 0123456789abcdef0123456789abcdef01234567\n", 2, "PR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* evidence: the heading is any level, Evidence at a word edge; a tilde fence works *)
fn test_evidence_edges (): bool =
  _body_is("Fixes #1\n#evidence\n~~~\n$ x\n~~~\n", 2, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes #1\n## Evidenced\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* the events: the findings printed, the status posted *)
fn test_events (): bool =
  _event_is("tests/events/pass.json", 0, "",
    "{\"state\":\"success\",\"context\":\"text-lint\",\"description\":\"the PR body is in form\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_is("tests/events/fail-refs.json", 0,
    "PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\n",
    "{\"state\":\"failure\",\"context\":\"text-lint\",\"description\":\"PR body: the first line is Fixes #N for the ticket, and the pull request meets the Done-when as written (first-line)\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_is("tests/events/exempt-relock.json", 0, "",
    "{\"state\":\"success\",\"context\":\"text-lint\",\"description\":\"exempt: a bot or a relock branch\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_is("tests/events/exempt-bot.json", 0, "",
    "{\"state\":\"success\",\"context\":\"text-lint\",\"description\":\"exempt: a bot or a relock branch\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_is("tests/events/fail-head-moved.json", 0,
    "PR body: it describes head 0123456789abcdef0123456789abcdef01234567 but the head is ffffffffffffffffffffffffffffffffffffffff; rewrite the body for the head (head)\n",
    "{\"state\":\"failure\",\"context\":\"text-lint\",\"description\":\"PR body: it describes head 0123456789abcdef0123456789abcdef01234567 but the head is ffffffffffffffffffffffffffffffffffffffff; rewrite the bo\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")

(* an event that is not a pull request event, or is not JSON, is refused: no status *)
fn test_refused_events (): bool =
  _event_is("tests/events/not-an-event.json", 1, "", "")
  && _event_is("tests/events/not-json.json", 1, "", "")

(* the exemption: a relock branch and a bot, nothing else *)
fn test_exemption_is_a_relock_branch_or_a_bot (): bool =
  _exempt_is("relock/2026-10-26", "moshez")
  && _exempt_is("work", "dependabot[bot]")
  && ~_exempt_is("work", "moshez")
  && ~_exempt_is("relock", "moshez")
  && ~_exempt_is("not-relock/x", "bot")
  && ~_exempt_is("", "")


(* phrases: the lines of phrases.txt are the rows of the original: each line has plus lines in the
   corpus that it finds alone and the oracle names with its row, the lint and the oracle agree on
   every line of the corpus, and every text row of the copy has its plus line, its minus line and
   its example; each of them says what it reached against what it read *)
fn test_phrases_equal_the_original (): bool = let
  val @(phrases_ok, phrases_array, phrases_used) = _file("phrases.txt")
  val @(corpus_ok, corpus_array, corpus_used) = _file("tests/original/corpus.txt")
  val @(oracle_ok, oracle_array, oracle_used) = _file("tests/original/oracle.txt")
  val @(tsv_ok, tsv_array, tsv_used) = _file("tests/original/phrases.tsv")
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(corpus_frozen, corpus_view) = $A.freeze<byte>(corpus_array)
  val @(oracle_frozen, oracle_view) = $A.freeze<byte>(oracle_array)
  val @(tsv_frozen, tsv_view) = $A.freeze<byte>(tsv_array)
  val phrases_read = _phrases_read(phrases_view, phrases_used, 0)
  val phrases_reached = _reach_phrases(corpus_view, corpus_used, phrases_view, phrases_used, 0, 1, oracle_view, oracle_used)
  val () = println! ("lines of phrases.txt reached: ", phrases_reached, " of ", phrases_read)
  val corpus_read = _lines_read(corpus_view, corpus_used, 0)
  val corpus_reached = _reach_corpus(corpus_view, corpus_used, 0, 1, phrases_view, phrases_used, oracle_view, oracle_used)
  val () = println! ("lines of the corpus compared with the oracle: ", corpus_reached, " of ", corpus_read)
  val rows_read = _rows_read(tsv_view, tsv_used, 0)
  val rows_reached = _reach_rows(corpus_view, corpus_used, tsv_view, tsv_used, 0)
  val () = println! ("text rows of the copy reached: ", rows_reached, " of ", rows_read)
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(corpus_frozen, corpus_view)
  val () = $A.free<byte>($A.thaw<byte>(corpus_frozen))
  val () = $A.drop<byte>(oracle_frozen, oracle_view)
  val () = $A.free<byte>($A.thaw<byte>(oracle_frozen))
  val () = $A.drop<byte>(tsv_frozen, tsv_view)
  val () = $A.free<byte>($A.thaw<byte>(tsv_frozen))
in
  phrases_ok && corpus_ok && oracle_ok && tsv_ok
  && phrases_read > 0 && phrases_reached = phrases_read
  && corpus_read > 0 && corpus_reached = corpus_read
  && rows_read > 0 && rows_reached = rows_read
end

(* #509, scratch-run. _gated_is gives lint_gated the event file's text as the body (the URL
   survives the quoting of JSON); the event cases below run the whole lint_event *)
fn test_gated_workflow_without_a_scratch_run_is_refused (): bool =
  _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-modified-gated.diff", 1,
    "PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-added-gated.diff", 1,
    "PR body: .github/workflows/new.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-renamed-gated.diff", 1,
    "PR body: .github/workflows/check-new-name.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-added-comment-only.diff", 1,
    "PR body: .github/workflows/new.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")

(* a job URL of relock-scratch in the body is the whole row; a run URL alone and a job of
   another repository are not *)
fn test_gated_workflow_with_a_scratch_run_passes (): bool =
  _gated_is("tests/events/gated-url.json", "tests/gated/changes-modified-gated.diff", 0, "")
  && _gated_is("tests/events/gated-url.json", "tests/gated/changes-added-gated.diff", 0, "")
  && _gated_is("tests/events/gated-run-url-only.json", "tests/gated/changes-modified-gated.diff", 1,
    "PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
  && _gated_is("tests/events/gated-url-other-repository.json", "tests/gated/changes-modified-gated.diff", 1,
    "PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")

(* end to end: the status is a failure with the finding when the event's body cites no run, a
   success when it cites one, and nothing changes for a pull request that changes no workflow *)
fn test_gated_event_status (): bool =
  _event_full("tests/events/gated-no-url.json", "tests/gated/changes-modified-gated.diff", 0,
    "PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n",
    "{\"state\":\"failure\",\"context\":\"text-lint\",\"description\":\"PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_full("tests/events/gated-url.json", "tests/gated/changes-modified-gated.diff", 0, "",
    "{\"state\":\"success\",\"context\":\"text-lint\",\"description\":\"the PR body is in form\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
  && _event_full("tests/events/gated-no-url.json", "tests/gated/changes-modified-plain.diff", 0, "",
    "{\"state\":\"success\",\"context\":\"text-lint\",\"description\":\"the PR body is in form\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")

(* a change that is not to a gated workflow needs no run: a plain workflow, a file that is not a
   workflow, a deleted workflow, no change at all *)
fn test_other_changes_need_no_scratch_run (): bool =
  _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-modified-plain.diff", 0, "")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-added-plain.diff", 0, "")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-other-file.diff", 0, "")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-deleted-gated.diff", 0, "")
  && _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-empty.diff", 0, "")

(* two changed files, one gated: one finding, for the gated one *)
fn test_one_finding_for_each_gated_file (): bool =
  _gated_is("tests/events/gated-no-url.json", "tests/gated/changes-two-files.diff", 1,
    "PR body: .github/workflows/check-gated.yml runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")

end
