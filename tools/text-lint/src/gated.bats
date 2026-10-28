(* gated -- a pull request that changes a workflow the base branch runs
   (bats-lang/repository-prototype#509). Keyword: text-lint gated.

   A workflow on a trigger that runs the default branch's file (pull_request_target,
   issue_comment, workflow_run, schedule and the others of gated-triggers.txt) has no run
   from a pull request that adds or changes it: text-lint (#487) merged with the lint tool run
   locally as its only evidence and failed on every pull request (#504). The row scratch-run
   refuses such a pull request body unless it cites a run of the change in bats-lang/relock-scratch:
   the run URL and the job URL (.../actions/runs/N/job/M). Two files are read, both made by the
   workflow with the GitHub API and git alone:

     the changes   for each file of the pull request under .github/workflows/, a line
                   "diff --git a/OLD b/NEW" and then the file's patch (an added file's patch is
                   all of it)
     the base      a checkout of the base commit; the copy of OLD there is the file that runs

   A changed file is gated when one of the events of gated-triggers.txt (the 21 of GitHub's table
   whose GITHUB_SHA is the default branch's, one name on each line) is a trigger of it, in its patch
   or in its base copy. A trigger is a key or a list item of the block of on:, a word of a flow
   list or of a single event after on:, or a word after "Called on:" in a comment (a reusable
   workflow names the event of its callers so); the same word as a permission (issues: write under
   permissions:), as an option of a trigger or in a step is not one. In a patch the block is read
   from the lines it shows: a hunk header ends it and git's text after the second @@ (the last
   line that starts a section, here on:) opens it again. A file with no base copy is new: only its
   patch is read. A deleted file (a hunk "+0,0 @@") runs nothing after the merge and is not gated.
   The URL is cited, not checked: the reviewer opens the run
   (the check needs the network, which text-lint does not use). *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "pattern.sats"
staload "support.sats"

fn _is_name_char (c: int): bool =
  (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c = 95

(* The end of the run of name characters that starts at i *)
fun _name_end {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i): [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if _is_name_char(byte2int0($A.read<byte>(text, i))) then _name_end(text, limit, i + 1)
  else i

(* The end of the run of spaces that starts at i *)
fun _skip_spaces {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i): [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if byte2int0($A.read<byte>(text, i)) = 32 then _skip_spaces(text, limit, i + 1)
  else i

(* Where the text literal first starts in text[i, limit), else the limit *)
fun _find_literal {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}{literal_len:nat}
  .<limit - i>.
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i, literal: string literal_len)
  : [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if starts_with(text, limit, i, literal) then i
  else _find_literal(text, limit, i + 1, literal)

(* Whether the byte wanted or the byte other is in text[i, limit) *)
fun _has_either {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i, wanted: int, other: int): bool =
  if i >= limit then false
  else let
    val c = byte2int0($A.read<byte>(text, i))
  in if c = wanted || c = other then true else _has_either(text, limit, i + 1, wanted, other) end

(* Whether text[i, limit) holds anything but spaces, a carriage return and a comment *)
fn _has_content {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i): bool = let
  val j = _skip_spaces(text, limit, i)
in
  if j >= limit then false
  else let
    val c = byte2int0($A.read<byte>(text, j))
  in c <> 35 && c <> 13 end
end

(* Whether text[ws, we) is the name of an event of the events file events[start, elimit): one
   name on each line, a line that starts with "#" is a note *)
fun _is_event {el,tl:agz}{en,tn:pos}{elimit:nat | elimit <= en}{start:nat | start <= elimit}
  {ws,we:nat | ws <= we; we <= tn} .<elimit - start>.
  (events: !$A.borrow(byte, el, en), elimit: int elimit, start: int start,
   text: !$A.borrow(byte, tl, tn), ws: int ws, we: int we): bool = let
  val raw = find_byte(events, elimit, start, 10)
  val here =
    (if raw <= start then false
     else if byte2int0($A.read<byte>(events, start)) = 35 then false
     else spans_equal(events, start, raw, text, ws, we)): bool
in
  if here then true
  else if raw >= elimit then false
  else _is_event(events, elimit, raw + 1, text, ws, we)
end

(* Whether a word of text[a, limit) up to a "#" is an event: a flow list, a single event or
   the words after "Called on:" *)
fun _words_gated {el,tl:agz}{en,tn:pos}{elimit:nat | elimit <= en}{limit:nat | limit <= tn}
  {a:nat | a <= limit} .<limit - a>.
  (events: !$A.borrow(byte, el, en), elimit: int elimit,
   text: !$A.borrow(byte, tl, tn), limit: int limit, a: int a): bool =
  if a >= limit then false
  else let
    val c = byte2int0($A.read<byte>(text, a))
  in
    if c = 35 then false
    else if _is_name_char(c) then let
      val e = _name_end(text, limit, a + 1)
    in
      if _is_event(events, elimit, 0, text, a, e) then true
      else _words_gated(events, elimit, text, limit, e)
    end
    else _words_gated(events, elimit, text, limit, a + 1)
  end

(* After "on:" of a line at column 0, the place after the key; a negative number when the line
   is not the key on *)
fn _on_rest {l:agz}{n:pos}{limit:nat | limit <= n}{c:nat | c <= limit}
  (text: !$A.borrow(byte, l, n), limit: int limit, c: int c)
  : [r:int | r < 0 || (c <= r && r <= limit)] int r =
  if c + 3 <= limit then
    (if starts_with(text, limit, c, "on:") then c + 3
     else if c + 5 <= limit then
       (if starts_with(text, limit, c, "\"on\":") then c + 5
        else if starts_with(text, limit, c, "'on':") then c + 5
        else ~1)
     else ~1)
  else ~1

(* Where the key or the item of a block line starts: after "- " when it is a list item *)
fn _item_start {l:agz}{n:pos}{raw:nat | raw <= n}{c0:nat | c0 <= raw}
  (text: !$A.borrow(byte, l, n), raw: int raw, c0: int c0): [x:nat | c0 <= x; x <= raw] int x =
  if c0 + 2 <= raw then
    (if starts_with(text, raw, c0, "- ") then _skip_spaces(text, raw, c0 + 2) else c0)
  else c0

(* The state after the line text[ls, raw) of a workflow: whether it names an event as a trigger,
   the mode (0 outside the key on, 1 in its block, 2 in a flow list or mapping that goes on) and
   the indentation of the block's keys (negative when not yet seen). A trigger is a key or a list
   item of the block of on: (indented once), the words of a flow list or of a single event after
   on:, or a word after "Called on:" in a comment; a permission (issues: write under
   permissions:) is in no such place. *)
fn _line {el,tl:agz}{en,tn:pos}{elimit:nat | elimit <= en}{raw:nat | raw <= tn}{ls:nat | ls <= raw}
  (events: !$A.borrow(byte, el, en), elimit: int elimit,
   text: !$A.borrow(byte, tl, tn), raw: int raw, ls: int ls, mode: int, baseline: int)
  : @(bool, int, int) = let
  val c0 = _skip_spaces(text, raw, ls)
in
  if c0 >= raw then @(false, mode, baseline)
  else let
    val c = byte2int0($A.read<byte>(text, c0))
  in
    if c = 13 then @(false, mode, baseline)
    else if c = 35 then let
      val p = _find_literal(text, raw, c0, "Called on:")
    in
      if p + 10 > raw then @(false, mode, baseline)
      else @(_words_gated(events, elimit, text, raw, p + 10), mode, baseline)
    end
    else if mode = 2 then
      @(_words_gated(events, elimit, text, raw, ls),
        (if _has_either(text, raw, ls, 93, 125) then 0 else 2), baseline)
    else if c0 = ls then let
      val r = _on_rest(text, raw, c0)
    in
      if r < 0 then @(false, 0, ~1)
      else if _words_gated(events, elimit, text, raw, r) then @(true, 0, ~1)
      else if ~_has_content(text, raw, r) then @(false, 1, ~1)
      else if _has_either(text, raw, r, 91, 123) && ~_has_either(text, raw, r, 93, 125) then
        @(false, 2, ~1)
      else @(false, 0, ~1)
    end
    else if mode = 1 then
      (if baseline >= 0 && c0 - ls > baseline then @(false, mode, baseline)
       else let
         val w = _item_start(text, raw, c0)
       in
         if w >= raw then @(false, mode, c0 - ls)
         else if ~_is_name_char(byte2int0($A.read<byte>(text, w))) then @(false, mode, c0 - ls)
         else let
           val e = _name_end(text, raw, w + 1)
         in @(_is_event(events, elimit, 0, text, w, e), mode, c0 - ls) end
       end)
    else @(false, mode, baseline)
  end
end

(* Where a patch's line starts its content: after the hunk header "@@ -a,b +c,d @@" and the
   space that follows (git puts the last line that starts a section of the file, here the key on:,
   after it), else after the one byte that says added, removed or kept *)
fn _content_start {l:agz}{n:pos}{raw:nat | raw <= n}{start:nat | start <= raw}
  (text: !$A.borrow(byte, l, n), raw: int raw, start: int start, hunk: bool)
  : [x:nat | start <= x; x <= raw] int x =
  if hunk then
    (if start + 2 > raw then raw
     else let
       val p = _find_literal(text, raw, start + 2, "@@")
     in
       if p + 2 >= raw then raw
       else if byte2int0($A.read<byte>(text, p + 2)) = 32 then p + 3
       else p + 2
     end)
  else if start < raw then start + 1 else raw

fn _line_start {l:agz}{n:pos}{raw:nat | raw <= n}{start:nat | start <= raw}
  (text: !$A.borrow(byte, l, n), raw: int raw, start: int start, patch: bool, hunk: bool)
  : [x:nat | start <= x; x <= raw] int x =
  if patch then _content_start(text, raw, start, hunk) else start

(* Whether the workflow text[start, hi) has an event of the events file as a trigger. The text
   is a file, or a patch (the lines have a byte before them that says added, removed or kept,
   a hunk header ends the block of on:, and its text after the second @@ is a line of the file
   at column 0). *)
fun _triggers_in {el,tl:agz}{en,tn:pos}{elimit:nat | elimit <= en}{hi:nat | hi <= tn}
  {start:nat | start <= hi} .<hi - start>.
  (events: !$A.borrow(byte, el, en), elimit: int elimit,
   text: !$A.borrow(byte, tl, tn), hi: int hi, start: int start, patch: bool,
   mode: int, baseline: int): bool =
  if start >= hi then false
  else let
    val raw = find_byte(text, hi, start, 10)
    val hunk = (patch && start + 2 <= raw && starts_with(text, raw, start, "@@")): bool
    val no_newline = (patch && start < raw && byte2int0($A.read<byte>(text, start)) = 92): bool
    val ls = _line_start(text, raw, start, patch, hunk)
    val @(found, mode2, baseline2) =
      (if no_newline then @(false, mode, baseline)
       else _line(events, elimit, text, raw, ls, (if hunk then 0 else mode),
         (if hunk then ~1 else baseline))): @(bool, int, int)
  in
    if found then true
    else if raw >= hi then false
    else _triggers_in(events, elimit, text, hi, raw + 1, patch, mode2, baseline2)
  end

(* The start of the first line at or after i that begins a file of the changes, else the limit *)
fun _next_header {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (diff: !$A.borrow(byte, l, n), limit: int limit, i: int i)
  : [j:nat | j <= limit; j >= i || j == limit] int j =
  if i >= limit then limit
  else let
    val raw = find_byte(diff, limit, i, 10)
  in
    if starts_with(diff, raw, i, "diff --git a/") then i
    else if raw >= limit then limit
    else _next_header(diff, limit, raw + 1)
  end

(* The end of the header line that starts at start, and the start of the next file's header (the
   limit when there is none) *)
fn _span_of_header {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start < limit}
  (diff: !$A.borrow(byte, l, n), limit: int limit, start: int start)
  : [he,nx:nat | start <= he; he <= limit; he <= nx; start < nx; nx <= limit] @(int he, int nx) = let
  val header_end = find_byte(diff, limit, start, 10)
in
  if header_end >= limit then @(header_end, limit)
  else let
    val following = _next_header(diff, limit, header_end + 1)
  in @(header_end, following) end
end

(* The place of " b/" in the header line diff[i, stop), else stop *)
fun _find_b {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (diff: !$A.borrow(byte, l, n), stop: int stop, i: int i): [j:nat | i <= j; j <= stop] int j =
  if i >= stop then stop
  else if starts_with(diff, stop, i, " b/") then i
  else _find_b(diff, stop, i + 1)

(* Whether a trigger of the events is in the file at base_dir/path, path being
   diff[path_start, path_stop); a file that cannot be read has no base copy *)
fn _base_has {dl,bl,pl:agz}{dn,bn,pn:pos}{plimit:nat | plimit <= pn}
  {path_start,path_stop:nat | path_start <= path_stop; path_stop <= dn}
  {base_len:nat | base_len <= bn}
  (diff: !$A.borrow(byte, dl, dn), path_start: int path_start, path_stop: int path_stop,
   base: !$A.borrow(byte, bl, bn), base_len: int base_len,
   events: !$A.borrow(byte, pl, pn), plimit: int plimit): bool =
  if base_len > 1000 then false
  else if path_stop - path_start > 1000 then false
  else let
    var path : $B.builder(0) = $B.create()
    val () = put_range(base, 0, base_len, path)
    val () = $B.put_char(path, 47)
    val () = put_range(diff, path_start, path_stop, path)
    val @(path_array, path_len) = $B.to_arr(path)
    val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
    var text : $B.builder(0) = $B.create()
    val @(ended, _) = read_file(path_view, path_len, text)
    val () = $A.drop<byte>(path_frozen, path_view)
    val () = $A.free<byte>($A.thaw<byte>(path_frozen))
    val @(text_array, text_len) = $B.to_arr(text)
    val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
    val found =
      (case+ ended of
       | Read_whole() => _triggers_in(events, plimit, text_view, text_len, 0, false, 0, ~1)
       | Read_too_long() => false
       | Read_failed() => false): bool
    val () = $A.drop<byte>(text_frozen, text_view)
    val () = $A.free<byte>($A.thaw<byte>(text_frozen))
  in found end

(* Whether the file of the section diff[header_end, section_end) (its header line is
   diff[header_start, header_end), b_at the place of " b/") is a workflow the base branch runs
   and the change keeps *)
fn _section_gated {dl,bl,pl:agz}{dn,bn,pn:pos}{plimit:nat | plimit <= pn}
  {header_start,b_at,header_end,section_end:nat | header_start + 13 <= b_at; b_at + 3 <= header_end;
   header_end <= section_end; section_end <= dn}{base_len:nat | base_len <= bn}
  (diff: !$A.borrow(byte, dl, dn), header_start: int header_start, b_at: int b_at,
   header_end: int header_end, section_end: int section_end,
   base: !$A.borrow(byte, bl, bn), base_len: int base_len,
   events: !$A.borrow(byte, pl, pn), plimit: int plimit): bool =
  if ~starts_with(diff, header_end, b_at + 3, ".github/workflows/") then false
  else if contains_text(diff, section_end, header_end, "+0,0 @@") then false
  else if _triggers_in(events, plimit, diff, section_end, header_end, true, 0, ~1) then true
  else _base_has(diff, header_start + 13, b_at, base, base_len, events, plimit)

(* The findings of the sections diff[start, limit): one for each gated file, its path in it *)
fun _sections {dl,bl,pl:agz}{dn,bn,pn:pos}{limit:nat | limit <= dn}{start:nat | start <= limit}
  {plimit:nat | plimit <= pn}{base_len:nat | base_len <= bn} .<limit - start>.
  (diff: !$A.borrow(byte, dl, dn), limit: int limit, start: int start,
   base: !$A.borrow(byte, bl, bn), base_len: int base_len,
   events: !$A.borrow(byte, pl, pn), plimit: int plimit, out: !$B.sized_rope, count: int): int =
  if start >= limit then count
  else let
    val @(header_end, next) = _span_of_header(diff, limit, start)
  in
    if start + 13 > header_end then
      _sections(diff, limit, next, base, base_len, events, plimit, out, count)
    else if ~starts_with(diff, header_end, start, "diff --git a/") then
      _sections(diff, limit, next, base, base_len, events, plimit, out, count)
    else let
      val b_at = _find_b(diff, header_end, start + 13)
    in
      if b_at + 3 > header_end then
        _sections(diff, limit, next, base, base_len, events, plimit, out, count)
      else if _section_gated(diff, start, b_at, header_end, next, base, base_len, events, plimit) then let
        val () = $B.sized_rope_bput(out, "PR body: ")
        val () = $B.sized_rope_copy(out, diff, b_at + 3, header_end)
        val () = $B.sized_rope_bput(out, " runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
      in _sections(diff, limit, next, base, base_len, events, plimit, out, count + 1) end
      else _sections(diff, limit, next, base, base_len, events, plimit, out, count)
    end
  end

(* The scratch-run pattern in an array: a job URL of bats-lang/relock-scratch *)
fn _run_pattern (): @([m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) = let
  var pattern : $B.builder(0) = $B.create()
  val () = $B.bput(pattern, "https://github.com/bats-lang/relock-scratch/actions/runs/\\d+/job/\\d+")
in $B.to_arr(pattern) end

(* The findings of the row scratch-run, appended to out: how many. The changes are
   changes[0, changes_len), the base checkout's directory is base[0, base_len), and the triggers
   are the pattern lines triggers[0, triggers_len). Nothing is read when the body cites a job of
   relock-scratch. *)
#pub fn lint_gated {bl,cl,dl,tl:agz}{bn,cn,dn,tn:pos}{len:nat | len <= bn}
  {changes_len:nat | changes_len <= cn}{base_len:nat | base_len <= dn}{triggers_len:nat | triggers_len <= tn}
  (body: !$A.borrow(byte, bl, bn), len: int len,
   changes: !$A.borrow(byte, cl, cn), changes_len: int changes_len,
   base: !$A.borrow(byte, dl, dn), base_len: int base_len,
   triggers: !$A.borrow(byte, tl, tn), triggers_len: int triggers_len,
   out: !$B.sized_rope): int

implement lint_gated (body, len, changes, changes_len, base, base_len, triggers, triggers_len, out) = let
  val @(pattern_array, pattern_len) = _run_pattern()
  val @(pattern_frozen, pattern_view) = $A.freeze<byte>(pattern_array)
  val cited = pattern_search(pattern_view, pattern_len, 0, body, 0, len) >= 0
  val () = $A.drop<byte>(pattern_frozen, pattern_view)
  val () = $A.free<byte>($A.thaw<byte>(pattern_frozen))
in
  if cited then 0
  else _sections(changes, changes_len, 0, base, base_len, triggers, triggers_len, out, 0)
end
