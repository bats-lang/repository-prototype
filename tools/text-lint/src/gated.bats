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

   A changed file is gated when a pattern of gated-triggers.txt (pattern.bats, one on each
   line, "#" lines are notes) is found in its patch or in its base copy. A file with no
   base copy is new: only its patch is searched. A deleted file (a hunk "+0,0 @@") runs nothing
   after the merge and is not gated. The URL is cited, not checked: the reviewer opens the run
   (the check needs the network, which text-lint does not use). *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "pattern.sats"
staload "support.sats"

(* Whether a pattern line of patterns[start, plimit) is found in text[lo, hi); a line that
   starts with "#" is a note *)
fun _any_pattern {pl,tl:agz}{pn,tn:pos}{plimit:nat | plimit <= pn}{start:nat | start <= plimit}
  {lo,hi:nat | lo <= hi; hi <= tn} .<plimit - start>.
  (patterns: !$A.borrow(byte, pl, pn), plimit: int plimit, start: int start,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi): bool = let
  val raw = find_byte(patterns, plimit, start, 10)
  val here =
    (if raw <= start then false
     else if byte2int0($A.read<byte>(patterns, start)) = 35 then false
     else pattern_search(patterns, raw, start, text, lo, hi) >= 0): bool
in
  if here then true
  else if raw >= plimit then false
  else _any_pattern(patterns, plimit, raw + 1, text, lo, hi)
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

(* Whether the pattern lines are found in the file at base_dir/path, path being
   diff[path_start, path_stop); a file that cannot be read has no base copy *)
fn _base_has {dl,bl,pl:agz}{dn,bn,pn:pos}{plimit:nat | plimit <= pn}
  {path_start,path_stop:nat | path_start <= path_stop; path_stop <= dn}
  {base_len:nat | base_len <= bn}
  (diff: !$A.borrow(byte, dl, dn), path_start: int path_start, path_stop: int path_stop,
   base: !$A.borrow(byte, bl, bn), base_len: int base_len,
   patterns: !$A.borrow(byte, pl, pn), plimit: int plimit): bool =
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
       | Read_whole() => _any_pattern(patterns, plimit, 0, text_view, 0, text_len)
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
   patterns: !$A.borrow(byte, pl, pn), plimit: int plimit): bool =
  if ~starts_with(diff, header_end, b_at + 3, ".github/workflows/") then false
  else if contains_text(diff, section_end, header_end, "+0,0 @@") then false
  else if _any_pattern(patterns, plimit, 0, diff, header_end, section_end) then true
  else _base_has(diff, header_start + 13, b_at, base, base_len, patterns, plimit)

(* The findings of the sections diff[start, limit): one for each gated file, its path in it *)
fun _sections {dl,bl,pl:agz}{dn,bn,pn:pos}{limit:nat | limit <= dn}{start:nat | start <= limit}
  {plimit:nat | plimit <= pn}{base_len:nat | base_len <= bn} .<limit - start>.
  (diff: !$A.borrow(byte, dl, dn), limit: int limit, start: int start,
   base: !$A.borrow(byte, bl, bn), base_len: int base_len,
   patterns: !$A.borrow(byte, pl, pn), plimit: int plimit, out: !$B.sized_rope, count: int): int =
  if start >= limit then count
  else let
    val @(header_end, next) = _span_of_header(diff, limit, start)
  in
    if start + 13 > header_end then
      _sections(diff, limit, next, base, base_len, patterns, plimit, out, count)
    else if ~starts_with(diff, header_end, start, "diff --git a/") then
      _sections(diff, limit, next, base, base_len, patterns, plimit, out, count)
    else let
      val b_at = _find_b(diff, header_end, start + 13)
    in
      if b_at + 3 > header_end then
        _sections(diff, limit, next, base, base_len, patterns, plimit, out, count)
      else if _section_gated(diff, start, b_at, header_end, next, base, base_len, patterns, plimit) then let
        val () = $B.sized_rope_bput(out, "PR body: ")
        val () = $B.sized_rope_copy(out, diff, b_at + 3, header_end)
        val () = $B.sized_rope_bput(out, " runs from the default branch: cite its job URL in bats-lang/relock-scratch (scratch-run)\n")
      in _sections(diff, limit, next, base, base_len, patterns, plimit, out, count + 1) end
      else _sections(diff, limit, next, base, base_len, patterns, plimit, out, count)
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
