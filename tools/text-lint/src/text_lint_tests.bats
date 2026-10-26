(* text_lint_tests -- the tests of text-lint (bats-lang/repository-prototype#487), run by
   `bats test` in tools/text-lint. Each check of the lint has a fixture body in tests/bodies
   (a pull request body as a file) and the cases below name the findings the lint gives it,
   word for word; the event cases run lint_event on the files of tests/events. The head is
   the constant _head () in every case. Keyword: text-lint tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "event.sats"
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
   tests/bodies/phrases.txt when phrases) gives that many findings and exactly that text *)
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
fn _event_is {path_len,findings_len,status_len:nat | path_len < 200}
  (path: string path_len, code: int, findings_text: string findings_len,
   status_text: string status_len): bool = let
  val @(event_ok, event_array, event_len) = _file(path)
  val @(phrases_array, phrases_len) = _text("")
  val @(url_array, url_len) = _text("https://github.com/o/r/actions/runs/1")
  val @(event_frozen, event_view) = $A.freeze<byte>(event_array)
  val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
  val @(url_frozen, url_view) = $A.freeze<byte>(url_array)
  val findings = $B.sized_rope_create()
  val status = $B.sized_rope_create()
  val got = lint_event(event_view, event_len, phrases_view, phrases_len, url_view, url_len,
    findings, status)
  val () = $A.drop<byte>(event_frozen, event_view)
  val () = $A.free<byte>($A.thaw<byte>(event_frozen))
  val () = $A.drop<byte>(phrases_frozen, phrases_view)
  val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
  val () = $A.drop<byte>(url_frozen, url_view)
  val () = $A.free<byte>($A.thaw<byte>(url_frozen))
  val same_findings = _rope_is(findings, findings_text)
  val same_status = _rope_is(status, status_text)
in event_ok && got = code && same_findings && same_status end

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

(* The phrases found in the body made of the two pieces by the phrases file of the lint *)
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
    "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\n")
  && _fixture_is("tests/bodies/fail-refs-other-repository.md", _head(), _test_phrases(), 1,
    "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\n")

(* one-ticket: two tickets *)
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

(* phrases: two patterns spell a letter as a class; the words are built here from pieces *)
fn test_class_spelled_patterns (): bool =
  (_real_hits("it is par", "tly done") = 1)
  && (_real_hits("par", "tially done") = 1)
  && (_real_hits("a ", "party") = 0)

(* an empty body fails every check but one-ticket *)
fn test_empty_body_fails_each_row (): bool =
  _fixture_is("tests/bodies/fail-empty.md", _head(), _test_phrases(), 4,
    "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* the edges of first-line: blank lines before, any case, the word edge, the digits *)
fn test_first_line_edges (): bool =
  _body_is("\n\nFixes #1\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("fixes #12\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes #\n", 4, "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fix #1\n", 4, "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* one-ticket: the same ticket twice, in two cases, is one ticket; Refixes is not Fixes *)
fn test_same_ticket_twice_is_one_ticket (): bool =
  _body_is("Fixes #1\nand fixes #1 again, and Refixes #2\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes a/b#1\nFixes A/B#1\n", 3, "PR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")
  && _body_is("Fixes a/b#1\nFixes a/b#2\n", 4, "PR body: Fixes names more than one ticket; one ticket, one PR, and a dependency is its own ticket and PR (one-ticket)\nPR body: no line Head: <the commit SHA>; the body names the head it describes (head)\nPR body: no Evidence heading; every claim has its command and raw output (evidence)\nPR body: it does not end with the generated-by footer of the template (footer)\n")

(* head: 41 digits are not a head; trailing blanks are fine; the last Head line counts *)
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
    "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\n",
    "{\"state\":\"failure\",\"context\":\"text-lint\",\"description\":\"PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (first-line)\",\"target_url\":\"https://github.com/o/r/actions/runs/1\"}\n")
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

end
