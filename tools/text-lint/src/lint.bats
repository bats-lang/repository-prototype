(* lint -- the form of a pull request body (bats-lang/repository-prototype#487).
   Keyword: text-lint rows.

   The rows are the ones of bats-lang/quire's tests/static/guidelines.py --pr-body, ported:

     row 1  the first line is "Fixes #N" (or "Fixes owner/repo#N"): a pull request that
            does not meet its Done-when as written is not opened as Refs
     row 2  the body names one ticket: every "Fixes <ticket>" is the same ticket
     row 3  a line "Head: <40 hex digits>" is there, and the last one is the head
     row 4  an Evidence heading, and a fenced block that starts with "$ <command>"
     row 5  the body ends with the footer of the template (one of three lines, below),
            holds exactly one, and no session URL
     row 6  none of the phrases of the phrases file (one text for each line, matched
            without regard to case, at word edges) is in the body

   A finding is one line of ASCII with no double quote. Lines end with LF or CRLF. The
   body, the head and the phrases are each in a buffer of at most 524288 bytes. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "support.sats"

fn _low (c: int): int = if c >= 65 && c <= 90 then c + 32 else c

(* kind 0: a word, a dot or a dash; 1: a digit; 2: a space or a tab; 3: a lowercase
   hex digit; 4: a word character (letter, digit, underscore); 5: a number sign *)
fn _is_class (c: int, kind: int): bool =
  if kind = 0 then
    ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c = 95
     || c = 46 || c = 45)
  else if kind = 1 then (c >= 48 && c <= 57)
  else if kind = 2 then (c = 32 || c = 9)
  else if kind = 3 then ((c >= 48 && c <= 57) || (c >= 97 && c <= 102))
  else if kind = 4 then
    ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c = 95)
  else c = 35

(* The end of the run of bytes of the kind that starts at i *)
fun _run {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, kind: int)
  : [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if _is_class(byte2int0($A.read<byte>(bytes, i)), kind) then
    _run(bytes, limit, i + 1, kind)
  else i

(* Whether the byte at i is the wanted one (false past the limit) *)
fn _is_at {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, wanted: int): bool =
  if i < limit then byte2int0($A.read<byte>(bytes, i)) = wanted else false

(* Whether the byte at i is of the kind (false past the limit) *)
fn _kind_at {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, kind: int): bool =
  if i < limit then _is_class(byte2int0($A.read<byte>(bytes, i)), kind) else false

fun _lit_at {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}{lit_len:nat}
  {at:nat | at <= lit_len} .<lit_len - at>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, literal: string lit_len,
   lit_len: int lit_len, at: int at, ci: bool): bool =
  if at >= lit_len then true
  else if i >= limit then false
  else let
    val c = byte2int0($A.read<byte>(bytes, i))
    val folded = (if ci then _low(c) else c): int
  in
    if folded = char2int0(string_get_at(literal, at)) then
      _lit_at(bytes, limit, i + 1, literal, lit_len, at + 1, ci)
    else false
  end

(* Whether the text literal starts at i (a literal in lowercase when ci) *)
fn _starts {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}{lit_len:nat}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, literal: string lit_len,
   ci: bool): bool =
  _lit_at(bytes, limit, i, literal, g1u2i(string1_length(literal)), 0, ci)

(* The end of a line without its CR: raw is where the LF is (or the limit) *)
fn _trim_cr {l:agz}{n:pos}{start:nat}
  {raw:nat | start <= raw; raw <= n}
  (bytes: !$A.borrow(byte, l, n), start: int start, raw: int raw)
  : [stop:nat | start <= stop; stop <= raw] int stop =
  if raw > start then
    (if byte2int0($A.read<byte>(bytes, raw - 1)) = 13 then raw - 1 else raw)
  else raw

(* The start of the first line that is not blank, else the limit *)
fun _first_line {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start <= limit}
  .<limit - start>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, start: int start)
  : [s:nat | s <= limit] int s =
  if start >= limit then limit
  else let
    val raw = find_byte(bytes, limit, start, 10)
    val stop = _trim_cr(bytes, start, raw)
    val blank_end = _run(bytes, stop, start, 2)
  in
    if blank_end >= stop then
      (if raw >= limit then limit else _first_line(bytes, limit, raw + 1))
    else start
  end

(* After "#", the end of its digits; fallback when there is none *)
fn _digits_after {l:agz}{n:pos}{limit:nat | limit <= n}{p:nat | p <= limit}{fallback:nat | fallback <= p}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, p: int p, fallback: int fallback)
  : [e:nat | fallback <= e; e <= limit] int e = let
  val e = _run(bytes, limit, p, 1)
in if e > p then e else fallback end

(* The end of a ticket reference that starts at j: owner/repo#digits or #digits; j when it is
   none *)
fn _ref_end {l:agz}{n:pos}{limit:nat | limit <= n}{j:nat | j <= limit}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, j: int j)
  : [e:nat | j <= e; e <= limit] int e = let
  val k = _run(bytes, limit, j, 0)
in
  if k > j then
    (if k >= limit then j
     else if ~_is_at(bytes, limit, k, 47) then j
     else let
       val m = _run(bytes, limit, k + 1, 0)
     in
       if m > k + 1 then
         (if m >= limit then j
          else if _is_at(bytes, limit, m, 35) then _digits_after(bytes, limit, m + 1, j)
          else j)
       else j
     end)
  else
    (if j >= limit then j
     else if _is_at(bytes, limit, j, 35) then _digits_after(bytes, limit, j + 1, j)
     else j)
end

(* "Fixes <ticket>" at i: the span of the ticket (empty when it is none) *)
fn _ticket_at {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i)
  : [rs,re:nat | rs <= re; re <= limit] @(int rs, int re) =
  if i + 5 > limit then @(0, 0)
  else if ~_starts(bytes, limit, i, "fixes", true) then @(0, 0)
  else let
    val j = _run(bytes, limit, i + 5, 2)
  in
    if j <= i + 5 then @(0, 0)
    else let
      val e = _ref_end(bytes, limit, j)
    in if e <= j then @(0, 0) else @(j, e) end
  end

(* Row 1: whether the first line starts with "Fixes <ticket>" *)
fn _first_line_fixes {l:agz}{n:pos}{limit:nat | limit <= n}
  (bytes: !$A.borrow(byte, l, n), limit: int limit): bool = let
  val s = _first_line(bytes, limit, 0)
in
  if s >= limit then false
  else let
    val @(rs, re) = _ticket_at(bytes, limit, s)
  in re > rs end
end

fun _ci_same {l:agz}{n:pos}{s1,s2,len:nat | s1 + len <= n; s2 + len <= n}{k:nat | k <= len}
  .<len - k>.
  (bytes: !$A.borrow(byte, l, n), s1: int s1, s2: int s2, len: int len, k: int k): bool =
  if k >= len then true
  else if _low(byte2int0($A.read<byte>(bytes, s1 + k)))
          = _low(byte2int0($A.read<byte>(bytes, s2 + k))) then
    _ci_same(bytes, s1, s2, len, k + 1)
  else false

fn _word_before {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i): bool =
  if i <= 0 then false else _kind_at(bytes, limit, i - 1, 4)

(* Row 2: whether a ticket named by "Fixes" anywhere in the body is not the first one named *)
fun _differs {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}
  {fs,fe:nat | fs <= fe; fe <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, fs: int fs, fe: int fe): bool =
  if i >= limit then false
  else if _word_before(bytes, limit, i) then _differs(bytes, limit, i + 1, fs, fe)
  else let
    val @(rs, re) = _ticket_at(bytes, limit, i)
  in
    if re <= rs then _differs(bytes, limit, i + 1, fs, fe)
    else if fe <= fs then _differs(bytes, limit, i + 1, rs, re)
    else if re - rs = fe - fs then
      (if _ci_same(bytes, rs, fs, re - rs, 0) then _differs(bytes, limit, i + 1, fs, fe)
       else true)
    else true
  end

(* Row 3: the start of the 40 digits of the last "Head:" line, else a negative number *)
fun _head_line {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start <= limit}
  {last:int | last < 0 || (last >= 0 && last + 40 <= limit)} .<limit - start>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, start: int start, last: int last)
  : [s:int | s < 0 || (s >= 0 && s + 40 <= limit)] int s = let
  val raw = find_byte(bytes, limit, start, 10)
  val stop = _trim_cr(bytes, start, raw)
  val here = (if start + 5 <= stop then
    (if _starts(bytes, stop, start, "Head:", false) then let
       val j = _run(bytes, stop, start + 5, 2)
       val k = _run(bytes, stop, j, 3)
     in
       if k - j = 40 then (if _run(bytes, stop, k, 2) >= stop then j else last) else last
     end
     else last)
    else last): [s:int | s < 0 || (s >= 0 && s + 40 <= limit)] int s
in
  if raw >= limit then here else _head_line(bytes, limit, raw + 1, here)
end

(* Row 4 heading: a line of "#"s, blanks, then Evidence at a word edge *)
fn _is_heading {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (bytes: !$A.borrow(byte, l, n), stop: int stop, start: int start): bool = let
  val h = _run(bytes, stop, start, 5)
in
  if h <= start then false
  else let
    val k = _run(bytes, stop, h, 2)
  in
    if k + 8 > stop then false
    else if _starts(bytes, stop, k, "evidence", true) then
      (if k + 8 = stop then true else ~_kind_at(bytes, stop, k + 8, 4))
    else false
  end
end

(* Row 4: bit 1 when a heading is there, bit 2 when a line "$ ..." follows a fence line *)
fun _evidence {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start <= limit}
  .<limit - start>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, start: int start, after_fence: bool,
   heading: bool, command: bool): int =
  if start >= limit then let
    val h = (if heading then 1 else 0): int
    val c = (if command then 2 else 0): int
  in h + c end
  else let
    val raw = find_byte(bytes, limit, start, 10)
    val stop = _trim_cr(bytes, start, raw)
    val is_heading = heading || _is_heading(bytes, stop, start)
    val is_command = command || (after_fence && _starts(bytes, stop, start, "$ ", false))
    val is_fence = _starts(bytes, stop, start, "```", false) || _starts(bytes, stop, start, "~~~", false)
  in
    if raw >= limit then _evidence(bytes, limit, limit, false, is_heading, is_command)
    else _evidence(bytes, limit, raw + 1, is_fence, is_heading, is_command)
  end

fun _rstrip {l:agz}{n:pos}{a:nat}{e:nat | a <= e; e <= n} .<e - a>.
  (bytes: !$A.borrow(byte, l, n), a: int a, e: int e): [x:nat | a <= x; x <= e] int x =
  if e <= a then a
  else if _is_class(byte2int0($A.read<byte>(bytes, e - 1)), 2) then _rstrip(bytes, a, e - 1)
  else e

(* Row 5: the number of lines that are a footer, and whether the last line that is not blank
   is one *)
fun _footers {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start <= limit}
  .<limit - start>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, start: int start, count: int,
   last_is: bool): @(int, bool) =
  if start >= limit then @(count, last_is)
  else let
    val raw = find_byte(bytes, limit, start, 10)
    val stop = _trim_cr(bytes, start, raw)
    val a = _run(bytes, stop, start, 2)
    val e = _rstrip(bytes, a, stop)
    val is_footer = (if e <= a then false
      else span_is(bytes, a, e, "🤖 Generated with [Claude Code](https://claude.ai/code)")
        || span_is(bytes, a, e, "🤖 Generated with [Claude Code](https://claude.com/claude-code)")
        || span_is(bytes, a, e, "_Generated by [Claude Code](https://claude.ai/code)_")): bool
    val count2 = (if is_footer then count + 1 else count): int
    val last2 = (if e <= a then last_is else is_footer): bool
  in
    if raw >= limit then @(count2, last2)
    else _footers(bytes, limit, raw + 1, count2, last2)
  end

(* Row 6: whether the phrase phrase[ps, pe) (compared without regard to case) is in the body
   at a word edge on each side *)
fun _ci_at {bl,pl:agz}{bn,pn:pos}{blimit:nat | blimit <= bn}{i:nat}{ps,plen:nat}
  {k:nat | k <= plen; i + plen <= blimit; ps + plen <= pn} .<plen - k>.
  (body: !$A.borrow(byte, bl, bn), blimit: int blimit, i: int i,
   phrase: !$A.borrow(byte, pl, pn), ps: int ps, plen: int plen, k: int k): bool =
  if k >= plen then true
  else if _low(byte2int0($A.read<byte>(body, i + k)))
          = _low(byte2int0($A.read<byte>(phrase, ps + k))) then
    _ci_at(body, blimit, i, phrase, ps, plen, k + 1)
  else false

fun _find_phrase {bl,pl:agz}{bn,pn:pos}{blimit:nat | blimit <= bn}{i:nat | i <= blimit}
  {ps:nat}{plen:pos | ps + plen <= pn} .<blimit - i>.
  (body: !$A.borrow(byte, bl, bn), blimit: int blimit, i: int i,
   phrase: !$A.borrow(byte, pl, pn), ps: int ps, plen: int plen): bool =
  if i + plen > blimit then false
  else if ~_word_before(body, blimit, i) && _ci_at(body, blimit, i, phrase, ps, plen, 0)
          && ~_kind_at(body, blimit, i + plen, 4) then true
  else _find_phrase(body, blimit, i + 1, phrase, ps, plen)

(* Appends the findings of the phrases file lines starting at start: a line is a phrase
   unless it is blank or starts with "#" *)
fun _phrases {bl,pl:agz}{bn,pn:pos}{blimit:nat | blimit <= bn}{plimit:nat | plimit <= pn}
  {start:nat | start <= plimit} .<plimit - start>.
  (body: !$A.borrow(byte, bl, bn), blimit: int blimit,
   phrases: !$A.borrow(byte, pl, pn), plimit: int plimit, start: int start,
   out: !$B.sized_rope): int =
  if start >= plimit then 0
  else let
    val raw = find_byte(phrases, plimit, start, 10)
    val stop = _trim_cr(phrases, start, raw)
    val a = _run(phrases, stop, start, 2)
    val e = _rstrip(phrases, a, stop)
    val found = (if e <= a then false
      else if byte2int0($A.read<byte>(phrases, a)) = 35 then false
      else _find_phrase(body, blimit, 0, phrases, a, e - a)): bool
    val () = if found then let
        val () = $B.sized_rope_bput(out, "PR body: it holds the phrase '")
        val () = $B.sized_rope_copy(out, phrases, a, e)
        val () = $B.sized_rope_bput(out, "', which the lint refuses (the phrases file)\n")
      in () end else ()
    val here = (if found then 1 else 0): int
  in
    if raw >= plimit then here
    else here + _phrases(body, blimit, phrases, plimit, raw + 1, out)
  end

(* The findings of the body body[0, len) for the head head[0, head_len) (an empty head is not
   compared) and the phrases phrases[0, phrases_len), one line each appended to out: how
   many *)
#pub fn lint_body {bl,hl,pl:agz}{bn,hn,pn:pos}{len:nat | len <= bn}{head_len:nat | head_len <= hn}
  {phrases_len:nat | phrases_len <= pn}
  (body: !$A.borrow(byte, bl, bn), len: int len, head: !$A.borrow(byte, hl, hn),
   head_len: int head_len, phrases: !$A.borrow(byte, pl, pn), phrases_len: int phrases_len,
   out: !$B.sized_rope): int

implement lint_body (body, len, head, head_len, phrases, phrases_len, out) = let
  val first_ok = _first_line_fixes(body, len)
  val () = if first_ok then () else
    $B.sized_rope_bput(out, "PR body: the first line is Fixes #N for the ticket; a PR that does not meet its Done-when as written is not opened as Refs (row 1)\n")
  val tickets_differ = _differs(body, len, 0, 0, 0)
  val () = if tickets_differ then
    $B.sized_rope_bput(out, "PR body: Fixes names more than one ticket; one ticket, one PR, and a dependency is its own ticket and PR (row 2)\n") else ()
  val head_at = _head_line(body, len, 0, ~1)
  val head_wrong = (if head_at < 0 then false
    else if head_len <= 0 then false
    else if head_len = 40 then ~spans_equal(body, head_at, head_at + 40, head, 0, head_len)
    else true): bool
  val head_missing = (head_at < 0): bool
  val () = if head_missing then
    $B.sized_rope_bput(out, "PR body: no line Head: <40-character SHA>; the body names the head it describes (row 3)\n") else ()
  val () = if head_at < 0 then () else if head_wrong then let
      val () = $B.sized_rope_bput(out, "PR body: it describes head ")
      val () = $B.sized_rope_copy(out, body, head_at, head_at + 40)
      val () = $B.sized_rope_bput(out, " but the head is ")
      val () = $B.sized_rope_copy(out, head, 0, head_len)
      val () = $B.sized_rope_bput(out, "; rewrite the body for the head (row 3)\n")
    in () end else ()
  val evidence = _evidence(body, len, 0, false, false, false)
  val () = if evidence = 0 || evidence = 2 then
    $B.sized_rope_bput(out, "PR body: no Evidence heading; every claim has its command and raw output (row 4)\n")
    else if evidence = 1 then
    $B.sized_rope_bput(out, "PR body: no fenced block that starts with $ <command> and holds its raw output (row 4)\n")
    else ()
  val @(footer_count, last_is_footer) = _footers(body, len, 0, 0, false)
  val () = if ~last_is_footer then
    $B.sized_rope_bput(out, "PR body: it does not end with the generated-by footer of the template (row 5)\n") else ()
  val () = if footer_count > 1 then
    $B.sized_rope_bput(out, "PR body: it holds more than one generated-by footer; exactly one (row 5)\n") else ()
  val session = contains_text(body, len, 0, "/code/session_")
  val () = if session then
    $B.sized_rope_bput(out, "PR body: it holds a session URL; the footer is the generated-by line alone (row 5)\n") else ()
  val phrase_count = _phrases(body, len, phrases, phrases_len, 0, out)
in
  let
    val a = (if first_ok then 0 else 1): int
    val b = (if tickets_differ then 1 else 0): int
    val c = (if head_missing then 1 else 0): int
    val d = (if head_wrong then 1 else 0): int
    val e = (if evidence = 3 then 0 else 1): int
    val f = (if last_is_footer then 0 else 1): int
    val g = (if footer_count > 1 then 1 else 0): int
    val h = (if session then 1 else 0): int
  in a + b + c + d + e + f + g + h + phrase_count end
end

(* Whether the pull request is exempt: the branch ref[0, ref_len) starts with relock/ or the
   login login[0, login_len) ends with [bot] *)
#pub fn is_exempt {rl,ll:agz}{rn,ln:pos}{ref_len:nat | ref_len <= rn}{login_len:nat | login_len <= ln}
  (ref: !$A.borrow(byte, rl, rn), ref_len: int ref_len,
   login: !$A.borrow(byte, ll, ln), login_len: int login_len): bool

implement is_exempt (ref, ref_len, login, login_len) =
  if _starts(ref, ref_len, 0, "relock/", false) then true
  else if login_len >= 5 then span_is(login, login_len - 5, login_len, "[bot]")
  else false
