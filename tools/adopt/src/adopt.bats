(* adopt -- adopts a template of tools/pin-audit/templates in repositories
   (bats-lang/repository-prototype#607). Keyword: adopt.

   adopt [--only NAME] [--as FILE] TEMPLATE COMMIT COMMENT NAME#TICKET...

   --as FILE is the name the template is written as in .github/workflows
   (relock-regenerate.yml is a form of relock.yml: --as relock.yml,
   bats-lang/repository-prototype#619); by default the template's own name.

   Run at the root of a checkout of repository-prototype. TEMPLATE is a file
   of tools/pin-audit/templates (canonical-files.yml, or
   ISSUE_TEMPLATE/<file>), COMMIT the repository-prototype commit (40
   lowercase hex digits) and COMMENT the version comment of the pin
   (`repository-prototype main <7 hex>`), the fill of the holes @@COMMIT@@
   and @@COMMENT@@ as the pin audit's tickets fill them. Each NAME#TICKET is
   a repository of the organisation and the ticket that asks it to adopt
   the template. For each repository adopt clones it into adopt-clones/NAME,
   writes the template with its holes filled at its path
   (.github/workflows/<file>, or .github/ISSUE_TEMPLATE/<file>) on the
   branch adopt-TICKET, pushes the branch and opens a draft pull request
   with the REST API (`gh api repos/bats-lang/NAME/pulls -X POST`, never
   `gh pr create`, which is GraphQL and refused; #611), whose body it makes
   (first line `Fixes bats-lang/NAME#TICKET`, Plan, Execution, Evidence,
   `Head:` and the footer), and prints a line for the repository: its pull
   request, its head and its state. A repository that already has the file as
   the template gives is left alone ("no-op"), and so is one whose branch is
   already pushed and has an open pull request; one whose branch is pushed
   with no open pull request gets the pull request opened from the branch's
   tip (the body made from that commit); one whose file differs is
   refused with the first byte that differs (the file is the repository's
   own to change, not adopt's). --only NAME does the one repository of the
   list and prints the file it wrote. The exit status is 1 when a
   repository is refused or failed, 2 for arguments it does not take.

   A @@MINUTE@@ hole (the minute of a relock's cron line, chosen once for a
   repository, bats-lang/repository-prototype#619) is filled for each
   repository from the file it has, by the rule of pin_audit --file-tickets:
   the digits (one or two) that follow the template's own text from the start
   of the line of the hole up to the hole when they are a number from 0 to 59
   followed by a byte that is no digit or name character, else 17 (99, 123, 5x). adopt prints the minute it
   used for each repository (`NAME: minute 41, ...`). A file that differs from
   the template is the repository's own and is refused, except when the
   template has a @@MINUTE@@ hole and the file has that cron line: it is a
   caller of this shape (an older form of the template), so it is replaced and
   the pull request shows the diff. Nothing here reads YAML.

   Bounds: a name, a template, a comment and a ticket are at most 255
   bytes, a text at most 524288 bytes. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use env as E
#use list as L
#use process as P
#use result as R

staload "support.sats"

(* A part of the arguments: where it starts and stops, at most 255 bytes *)
typedef range (n:int) = [s,e:nat | s <= e; e <= n; e - s <= 255] @(int s, int e)

(* ============================================================
   The command line
   ============================================================ *)

(* The place where the argument that starts at at stops: its start when it is missing or longer than 255 bytes *)
fn _arg_stop {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{at:nat | at <= len}
  (a: !$A.borrow(byte, l, n), len: int len, at: int at): [e:nat | at <= e; e <= len; e - at <= 255] int e = let
  val stop = find_byte(a, len, at, 0)
in if stop - at > 255 then at else stop end

(* The place where the argument after the one that starts at at starts *)
fn _arg_next {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{at:nat | at <= len}
  (a: !$A.borrow(byte, l, n), len: int len, at: int at): [next:nat | next <= len; at >= len || at < next] int next = let
  val stop = find_byte(a, len, at, 0)
in if stop >= len then len else stop + 1 end

(* The argument that starts at at: whether it is there (not empty, not too long), its range, and where the next starts *)
fn _take {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{at:nat | at <= len}
  (a: !$A.borrow(byte, l, n), len: int len, at: int at): @(bool, range(n), [next:nat | next <= len; at >= len || at < next] int next) = let
  val stop = _arg_stop(a, len, at)
  val next = _arg_next(a, len, at)
in @(stop > at, @(at, stop), next) end

(* The place of the first argument after the program's own name *)
fn _after_program {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}
  (a: !$A.borrow(byte, l, n), len: int len): [after:nat | after <= len] int after = let
  val stop = find_byte(a, len, 0, 0)
in if stop >= len then len else stop + 1 end

(* Whether the range is a template name: a file name, or ISSUE_TEMPLATE/ and a file name; and which *)
fn _template_kind {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), template: range(n)): @(bool, bool) = let
  val @(ts, te) = template
  val issue_end = lit_step(a, te, ts, "ISSUE_TEMPLATE/")
in
  if issue_end >= 0 then @(issue_end < te && class_end(a, te, issue_end, Class_name()) = te, true)
  else @(ts < te && class_end(a, te, ts, Class_name()) = te, false)
end

(* Whether the range is 40 lowercase hexadecimal digits *)
fn _is_commit {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), commit: range(n)): bool = let
  val @(cs, ce) = commit
in hex_step(a, ce, cs, 40) >= 0 && ce = cs + 40 end

(* Whether the range is printable ASCII, not empty *)
fn _is_comment {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), comment: range(n)): bool = let
  val @(ms, me) = comment
in ms < me && class_end(a, me, ms, Class_printable()) = me end

(* NAME#TICKET at at: whether it is one (a name of letters, digits and . _ -, a hash, one to nine digits), the name, the ticket, and where the next starts *)
fn _entry {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{at:nat | at <= len}
  (a: !$A.borrow(byte, l, n), len: int len, at: int at)
  : @(bool, range(n), range(n), [next:nat | next <= len; at >= len || at < next] int next) = let
  val stop = _arg_stop(a, len, at)
  val next = _arg_next(a, len, at)
  val hash = find_byte(a, stop, at, 35)
in
  if hash >= stop then @(false, @(0, 0), @(0, 0), next)
  else if hash <= at then @(false, @(0, 0), @(0, 0), next)
  else if class_end(a, hash, at, Class_name()) != hash then @(false, @(0, 0), @(0, 0), next)
  else let
    val digits_end = class_end(a, stop, hash + 1, Class_digit())
  in
    if digits_end != stop then @(false, @(0, 0), @(0, 0), next)
    else if stop - (hash + 1) < 1 then @(false, @(0, 0), @(0, 0), next)
    else if stop - (hash + 1) > 9 then @(false, @(0, 0), @(0, 0), next)
    else @(true, @(at, hash), @(hash + 1, stop), next)
  end
end

(* Whether two ranges of the arguments are the same text *)
fn _same {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), left: range(n), right: range(n)): bool = let
  val @(ls, le) = left
  val @(rs, re) = right
in if le - ls = re - rs then range_eq_in(a, ls, le, rs) else false end

(* The entries from at: ~1 when one is not NAME#TICKET, else how many are run (all of them, or those named only) *)
fun _survey {l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{at:nat | at <= len} .<len - at>.
  (a: !$A.borrow(byte, l, n), len: int len, at: int at, has_only: bool, only: range(n), count: int): int =
  if at >= len then count
  else let
    val @(ok, name, _, next) = _entry(a, len, at)
  in
    if ~ok then ~1
    else let
      val rest = _survey(a, len, next, has_only, only, (if ~has_only || _same(a, name, only) then count + 1 else count))
    in rest end
  end

(* ============================================================
   The file: a template with its holes filled
   ============================================================ *)

(* The start of the line of t[0, tlen) that holds the place at *)
fun _line_start {l:agz}{n:pos}{tlen:nat | tlen <= n}{at:nat | at <= tlen} .<at>.
  (t: !$A.borrow(byte, l, n), tlen: int tlen, at: int at): [start:nat | start <= at] int start =
  if at <= 0 then 0
  else if byte2int0($A.read<byte>(t, at - 1)) = 10 then at
  else _line_start(t, tlen, at - 1)

(* The first place at or after at of t[0, tlen) where the minute hole begins, or ~1 *)
fun _hole_at {l:agz}{n:pos}{tlen:nat | tlen <= n}{at:nat | at <= tlen} .<tlen - at>.
  (t: !$A.borrow(byte, l, n), tlen: int tlen, at: int at): [hole:int | hole < 0 || (hole >= at && hole <= tlen)] int hole =
  if at >= tlen then ~1
  else if lit_step(t, tlen, at, "@@MINUTE@@") >= 0 then at
  else _hole_at(t, tlen, at + 1)

(* The first place p at or after from of e[0, elen) that holds t[prefix_start, hole) and then a digit: the place of the
   digits (at most two) and how many, none is a count of 0, and whether they are a minute (minute_ok: 0 to 59, then no digit or name
   character; the line is found either way, so the file is a caller of this shape, and the minute used is 17 when it is not) *)
fun _find_minute {t_l,e_l:agz}{elen:nat | elen <= 524288}{prefix_start,hole:nat | prefix_start <= hole; hole <= 524288}{from:nat | from <= elen} .<elen - from>.
  (t: !$A.borrow(byte, t_l, 524288), prefix_start: int prefix_start, hole: int hole,
   e: !$A.borrow(byte, e_l, 524288), elen: int elen, from: int from)
  : [digits_start,digit_count:nat | digit_count <= 2; digits_start + digit_count <= elen] @(int digits_start, int digit_count, bool) =
  if from >= elen then @(0, 0, false)
  else let
    val digits_at = from + (hole - prefix_start)
  in
    if digits_at > elen then @(0, 0, false)
    else if range_eq(t, prefix_start, hole, e, from) then let
      val counted = digits_upto_two(e, elen, digits_at)
    in
      if counted >= 1 then @(digits_at, counted, minute_ok(e, elen, digits_at, counted))
      else _find_minute(t, prefix_start, hole, e, elen, from + 1)
    end
    else _find_minute(t, prefix_start, hole, e, elen, from + 1)
  end

(* The place and the count (at most two) of the digits the file e[0, elen) has for the template's first minute hole
   (pin_audit --file-tickets' rule); a count of 0 when the template has no hole, the file was not read whole or it has no such line *)
fn _minute_of {t_l,e_l:agz}{tlen,elen:nat | tlen <= 524288; elen <= 524288}
  (t: !$A.borrow(byte, t_l, 524288), tlen: int tlen, e: !$A.borrow(byte, e_l, 524288), elen: int elen, e_whole: bool)
  : [digits_start,digit_count:nat | digit_count <= 2; digits_start + digit_count <= elen] @(int digits_start, int digit_count, bool) = let
  val hole = _hole_at(t, tlen, 0)
in
  if ~e_whole then @(0, 0, false)
  else if hole < 0 then @(0, 0, false)
  else let
    val prefix_start = _line_start(t, tlen, hole)
  in _find_minute(t, prefix_start, hole, e, elen, 0) end
end

(* The template t[at, tlen) written to out with @@COMMIT@@ replaced by a[cs, ce), @@COMMENT@@ by a[ms, me) and @@MINUTE@@ by
   e[es, ee), or by 17 when no_minute *)
fun _fill {t_l,a_l,e_l:agz}{tlen:nat | tlen <= 524288}{n:pos}{cs,ce,ms,me:nat | cs <= ce; ce <= n; ms <= me; me <= n}{es,ee:nat | es <= ee; ee <= 524288}{at:nat | at <= tlen} .<tlen - at>.
  (t: !$A.borrow(byte, t_l, 524288), tlen: int tlen, at: int at, out: !$B.sized_rope,
   a: !$A.borrow(byte, a_l, n), cs: int cs, ce: int ce, ms: int ms, me: int me,
   e: !$A.borrow(byte, e_l, 524288), es: int es, ee: int ee, no_minute: bool): void =
  if at >= tlen then ()
  else let
    val commit_end = lit_step(t, tlen, at, "@@COMMIT@@")
  in
    if commit_end >= 0 then let
      val () = $B.sized_rope_copy(out, a, cs, ce)
    in _fill(t, tlen, commit_end, out, a, cs, ce, ms, me, e, es, ee, no_minute) end
    else let
      val comment_end = lit_step(t, tlen, at, "@@COMMENT@@")
    in
      if comment_end >= 0 then let
        val () = $B.sized_rope_copy(out, a, ms, me)
      in _fill(t, tlen, comment_end, out, a, cs, ce, ms, me, e, es, ee, no_minute) end
      else let
        val minute_end = lit_step(t, tlen, at, "@@MINUTE@@")
      in
        if minute_end >= 0 then let
          val () = (if no_minute then $B.sized_rope_bput(out, "17") else $B.sized_rope_copy(out, e, es, ee))
        in _fill(t, tlen, minute_end, out, a, cs, ce, ms, me, e, es, ee, no_minute) end
        else let
          val () = $B.sized_rope_put(out, $AR.low_byte(byte2int0($A.read<byte>(t, at))))
        in _fill(t, tlen, at + 1, out, a, cs, ce, ms, me, e, es, ee, no_minute) end
      end
    end
  end

(* The first place where e[0, x) and f[0, y) differ, else ~1 when they are the same text *)
fun _differ {e_l,f_l:agz}{x,y:nat | x <= 524288; y <= 524288}{i:nat | i <= x; i <= y} .<x - i>.
  (e: !$A.borrow(byte, e_l, 524288), x: int x, f: !$A.borrow(byte, f_l, 524288), y: int y, i: int i): int =
  if i >= x then (if x = y then ~1 else i)
  else if i >= y then i
  else if byte2int0($A.read<byte>(e, i)) = byte2int0($A.read<byte>(f, i)) then _differ(e, x, f, y, i + 1)
  else i

(* ============================================================
   The paths and the arguments of one repository
   ============================================================ *)

(* adopt-clones/NAME and the suffix, as an argument *)
fn _clone_arg {l:agz}{n:pos | n <= 4096}{suffix_len:nat | suffix_len <= 1000}
  (a: !$A.borrow(byte, l, n), name: range(n), suffix: string suffix_len): $P.arg_entry = let
  val @(ns, ne) = name
in arg_range("adopt-clones/", a, ns, ne, suffix) end

(* The file in the clone: adopt-clones/NAME/.github/workflows/<target>, or .github/ISSUE_TEMPLATE/<file> *)
fn _target_path {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n), target: range(n), is_issue: bool): path_text = let
  val @(ns, ne) = name
  val @(ts, te) = target
in
  if is_issue then let
    var out : $B.builder(0) = $B.create()
    val () = $B.bput(out, "adopt-clones/")
    val () = put_range(a, ns, ne, out)
    val () = $B.bput(out, "/.github/")
    val () = put_range(a, ts, te, out)
    val @(arr, k) = $B.to_arr(out)
  in @(arr, k) end
  else let
    var out : $B.builder(0) = $B.create()
    val () = $B.bput(out, "adopt-clones/")
    val () = put_range(a, ns, ne, out)
    val () = $B.bput(out, "/.github/workflows/")
    val () = put_range(a, ts, te, out)
    val @(arr, k) = $B.to_arr(out)
  in @(arr, k) end
end

(* The file's path in the repository: .github/workflows/<target>, or .github/<ISSUE_TEMPLATE/file> *)
fn _relative_arg {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), target: range(n), is_issue: bool): $P.arg_entry = let
  val @(ts, te) = target
in
  if is_issue then arg_range(".github/", a, ts, te, "")
  else arg_range(".github/workflows/", a, ts, te, "")
end

(* The directory of the file in the clone *)
fn _directory_arg {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n), is_issue: bool): $P.arg_entry =
  if is_issue then _clone_arg(a, name, "/.github/ISSUE_TEMPLATE")
  else _clone_arg(a, name, "/.github/workflows")

(* The path of the template in this checkout *)
fn _template_path {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), template: range(n)): path_text = let
  val @(ts, te) = template
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, "tools/pin-audit/templates/")
  val () = put_range(a, ts, te, out)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* `Adopt <template> at repository-prototype <commit>`: the commit's message and the pull request's title *)
fn _title_arg {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), template: range(n), commit: range(n)): $P.arg_entry = let
  val @(ts, te) = template
  val @(cs, ce) = commit
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, "Adopt ")
  val () = put_range(a, ts, te, out)
  val () = $B.bput(out, " at repository-prototype ")
  val () = put_range(a, cs, ce, out)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* `title=Adopt <template> at repository-prototype <commit>`: the title as a field of gh api *)
fn _title_field {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), template: range(n), commit: range(n)): $P.arg_entry = let
  val @(ts, te) = template
  val @(cs, ce) = commit
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, "title=Adopt ")
  val () = put_range(a, ts, te, out)
  val () = $B.bput(out, " at repository-prototype ")
  val () = put_range(a, cs, ce, out)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* ============================================================
   The pull request's body
   ============================================================ *)

(* The body: its first line, Plan, Execution, Evidence (the two commands adopt ran, with their output), the Head line and the footer *)
fn _body {l,head_l,stat_l:agz}{n:pos | n <= 4096}{stat_len:nat | stat_len <= 524288}
  (a: !$A.borrow(byte, l, n), name: range(n), ticket: range(n), template: range(n), target: range(n), commit: range(n), comment: range(n), is_issue: bool,
   head: !$A.borrow(byte, head_l, 524288), stat: !$A.borrow(byte, stat_l, 524288), stat_len: int stat_len): $B.sized_rope = let
  val @(ns, ne) = name
  val @(ks, ke) = ticket
  val @(ts, te) = template
  val @(gs, ge) = target
  val @(cs, ce) = commit
  val @(ms, me) = comment
  var body : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(body, "Fixes bats-lang/")
  val () = $B.sized_rope_copy(body, a, ns, ne)
  val () = $B.sized_rope_bput(body, "#")
  val () = $B.sized_rope_copy(body, a, ks, ke)
  val () = $B.sized_rope_bput(body, "\n\nAdopts `")
  val () = $B.sized_rope_copy(body, a, ts, te)
  val () = $B.sized_rope_bput(body, "` of bats-lang/repository-prototype at `")
  val () = $B.sized_rope_copy(body, a, cs, ce)
  val () = $B.sized_rope_bput(body, "` in this repository. `adopt` (tools/adopt of repository-prototype) made this pull request: it wrote the file from the template and did not type it.\n\n## Plan\n\nDone when: the file `")
  val () = (if is_issue then $B.sized_rope_bput(body, ".github/") else $B.sized_rope_bput(body, ".github/workflows/"))
  val () = $B.sized_rope_copy(body, a, gs, ge)
  val () = $B.sized_rope_bput(body, "` is `tools/pin-audit/templates/")
  val () = $B.sized_rope_copy(body, a, ts, te)
  val () = $B.sized_rope_bput(body, "` of bats-lang/repository-prototype at `")
  val () = $B.sized_rope_copy(body, a, cs, ce)
  val () = $B.sized_rope_bput(body, "` with its holes filled.\n\n1. `git show --stat --format= HEAD` shows the one file this pull request adds.\n2. CI of the head, workflow `canonical-files.yml`, job `canonical-files`, step `Refuse a changed file that is not canonical`, greppable `== canonical-files`: the step prints that line with 0 not canonical when the file equals the template with its holes filled (found with the run and job of the head under actions).\n\n## Execution\n\n`adopt` cloned bats-lang/")
  val () = $B.sized_rope_copy(body, a, ns, ne)
  val () = $B.sized_rope_bput(body, ", filled `@@COMMIT@@` with `")
  val () = $B.sized_rope_copy(body, a, cs, ce)
  val () = $B.sized_rope_bput(body, "` and `@@COMMENT@@` with `")
  val () = $B.sized_rope_copy(body, a, ms, me)
  val () = $B.sized_rope_bput(body, "`, wrote the file on the branch `adopt-")
  val () = $B.sized_rope_copy(body, a, ks, ke)
  val () = $B.sized_rope_bput(body, "`, committed and pushed it, and opened this draft pull request.\n\n## Evidence\n\n```\n$ git rev-parse HEAD\n")
  val () = $B.sized_rope_copy(body, head, 0, 40)
  val () = $B.sized_rope_bput(body, "\n$ git show --stat --format= HEAD\n")
  val () = $B.sized_rope_copy(body, stat, 0, stat_len)
  val () = $B.sized_rope_bput(body, "```\n\nHead: ")
  val () = $B.sized_rope_copy(body, head, 0, 40)
  val () = $B.sized_rope_bput(body, "\n\n🤖 Generated with [Claude Code](https://claude.com/claude-code)\n")
in body end

(* ============================================================
   One repository
   ============================================================ *)

(* The path of the file in the repository, printed *)
fn _print_path {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), target: range(n), is_issue: bool): void = let
  val @(ts, te) = target
  val () = print! (".github/")
  val () = if is_issue then () else print! ("workflows/")
in print_range(a, ts, te) end

(* The start of the line of a repository: `NAME: ` *)
fn _line {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n)): void = let
  val @(ns, ne) = name
  val () = print_range(a, ns, ne)
in print! (": ") end

(* A step that failed: the line of the repository says so; the failure is counted (1) *)
fn _fail {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n), step: string, status: int): int = let
  val () = _line(a, name)
  val () = println! ("- - failed: ", step, " (status ", status, ")")
in 1 end

(* git -C <the clone> and the arguments *)
fn _git_in {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n), rest: $L.listv($P.arg_entry)): $L.listv($P.arg_entry) =
  $L.list_vt_cons(arg_text("-C"), $L.list_vt_cons(_clone_arg(a, name, ""), rest))

(* The path of the file the body is written to: adopt-clones/NAME.body.md *)
fn _body_path {l:agz}{n:pos | n <= 4096} (a: !$A.borrow(byte, l, n), name: range(n)): path_text = let
  val @(ns, ne) = name
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, "adopt-clones/")
  val () = put_range(a, ns, ne, out)
  val () = $B.bput(out, ".body.md")
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* Two arguments in front of the rest of a list *)
fn _push2 (x: $P.arg_entry, y: $P.arg_entry, rest: $L.listv($P.arg_entry)): $L.listv($P.arg_entry) =
  $L.list_vt_cons(x, $L.list_vt_cons(y, rest))

(* The pull request of the branch adopt-TICKET at its tip rev (HEAD of the clone, or FETCH_HEAD of a branch fetched), with the REST API
   (keyword: rest pull request; gh pr create is GraphQL, which is refused): the head, the push (when push), the body and gh api; the failures counted *)
fn _open {a_l:agz}{n:pos | n <= 4096}{rev_len:nat | rev_len <= 1000}
  (a: !$A.borrow(byte, a_l, n), name: range(n), ticket: range(n), template: range(n), target: range(n), is_issue: bool, commit: range(n), comment: range(n),
   rev: string rev_len, push: bool): int = let
  val @(ns, ne) = name
  val @(ks, ke) = ticket
  var head : $B.builder(0) = $B.create()
          val @(parsed, _) = capture_with("git", $L.list_vt_cons(arg_text("git"), _git_in(a, name, args2(arg_text("rev-parse"), arg_text(rev)))), no_arguments(), head)
          val @(head_array, head_len) = $B.to_arr(head)
          val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
          val head_ok = (parsed = 0 && hex_step(head_view, head_len, 0, 40) >= 0): bool
          val result =
            (if ~head_ok then _fail(a, name, "git rev-parse", parsed)
             else let
               val pushed =
                 (if push then run_program("git", _git_in(a, name, $L.list_vt_cons(arg_text("push"), args3(arg_text("--quiet"), arg_text("origin"), arg_range("adopt-", a, ks, ke, ""))))) else 0): int
             in
               if pushed != 0 then _fail(a, name, "git push", pushed)
               else let
                 var stat : $B.builder(0) = $B.create()
                 val @(shown, _) = capture_with("git", $L.list_vt_cons(arg_text("git"), _git_in(a, name, $L.list_vt_cons(arg_text("show"), args3(arg_text("--stat"), arg_text("--format="), arg_text(rev))))), no_arguments(), stat)
                 val @(stat_array, stat_len) = $B.to_arr(stat)
                 val @(stat_frozen, stat_view) = $A.freeze<byte>(stat_array)
                 val written =
                   (if shown != 0 then false
                    else write_rope(_body_path(a, name), _body(a, name, ticket, template, target, commit, comment, is_issue, head_view, stat_view, stat_len))): bool
                 val result =
                   (if ~written then _fail(a, name, "writing the body", shown)
                    else let
                      var url : $B.builder(0) = $B.create()
                      val @(opened, _) = capture_with("gh",
                        $L.list_vt_cons(arg_text("gh"),
                        _push2(arg_text("api"), arg_range("repos/bats-lang/", a, ns, ne, "/pulls"),
                        _push2(arg_text("-X"), arg_text("POST"),
                        _push2(arg_text("-f"), _title_field(a, template, commit),
                        _push2(arg_text("-f"), arg_range("head=adopt-", a, ks, ke, ""),
                        _push2(arg_text("-f"), arg_text("base=main"),
                        _push2(arg_text("-F"), arg_text("draft=true"),
                        _push2(arg_text("-F"), arg_range("body=@adopt-clones/", a, ns, ne, ".body.md"),
                        args2(arg_text("--jq"), arg_text(".html_url")))))))))),
                        no_arguments(), url)
                      val @(url_array, url_len) = $B.to_arr(url)
                      val @(url_frozen, url_view) = $A.freeze<byte>(url_array)
                      val url_stop = find_byte(url_view, url_len, 0, 10)
                      val result =
                        (if opened != 0 then _fail(a, name, "gh api pulls", opened)
                         else if url_stop <= 0 then _fail(a, name, "gh api pulls printed no pull request", opened)
                         else let
                           val () = _line(a, name)
                           val () = print_range(url_view, 0, url_stop)
                           val () = print! (" ")
                           val () = print_range(head_view, 0, 40)
                         in (println! (" draft"); 0) end): int
                      val () = $A.drop<byte>(url_frozen, url_view)
                      val () = $A.free<byte>($A.thaw<byte>(url_frozen))
                    in result end): int
                 val () = $A.drop<byte>(stat_frozen, stat_view)
                 val () = $A.free<byte>($A.thaw<byte>(stat_frozen))
               in result end
             end): int
          val () = $A.drop<byte>(head_frozen, head_view)
          val () = $A.free<byte>($A.thaw<byte>(head_frozen))
in result end

(* The branch is already pushed: its open pull request, if it has one, is left alone (and said); else the pull request is opened from the branch's tip *)
fn _resume {a_l:agz}{n:pos | n <= 4096}
  (a: !$A.borrow(byte, a_l, n), name: range(n), ticket: range(n), template: range(n), target: range(n), is_issue: bool, commit: range(n), comment: range(n)): int = let
  val @(ns, ne) = name
  val @(ks, ke) = ticket
  var found : $B.builder(0) = $B.create()
  val @(listed, _) = capture_with("gh",
    $L.list_vt_cons(arg_text("gh"),
    _push2(arg_text("api"), arg_range("repos/bats-lang/", a, ns, ne, "/pulls"),
    _push2(arg_text("-X"), arg_text("GET"),
    _push2(arg_text("-f"), arg_range("head=bats-lang:adopt-", a, ks, ke, ""),
    _push2(arg_text("-f"), arg_text("state=open"),
    args2(arg_text("--jq"), arg_text(".[] | .html_url"))))))),
    no_arguments(), found)
  val @(found_array, found_len) = $B.to_arr(found)
  val @(found_frozen, found_view) = $A.freeze<byte>(found_array)
  val found_stop = find_byte(found_view, found_len, 0, 10)
  val result =
    (if listed != 0 then _fail(a, name, "gh api pulls list", listed)
     else if found_len > 0 then
       (if found_stop <= 0 then _fail(a, name, "gh api pulls list printed no address", listed)
        else let
          val () = _line(a, name)
          val () = print! ("- - no-op: the branch is already pushed and has the open pull request ")
          val () = print_range(found_view, 0, found_stop)
        in (println! (); 0) end)
     else let
       val fetched = run_program("git", _git_in(a, name, $L.list_vt_cons(arg_text("fetch"), args3(arg_text("--quiet"), arg_text("origin"), arg_range("adopt-", a, ks, ke, "")))))
     in
       if fetched != 0 then _fail(a, name, "git fetch", fetched)
       else _open(a, name, ticket, template, target, is_issue, commit, comment, "FETCH_HEAD", false)
     end): int
  val () = $A.drop<byte>(found_frozen, found_view)
  val () = $A.free<byte>($A.thaw<byte>(found_frozen))
in result end

(* The pull request, once the file is written in the clone: a branch not pushed is made, committed, pushed and opened; one pushed is resumed *)
fn _publish {a_l:agz}{n:pos | n <= 4096}
  (a: !$A.borrow(byte, a_l, n), name: range(n), ticket: range(n), template: range(n), target: range(n), is_issue: bool, commit: range(n), comment: range(n)): int = let
  val @(ks, ke) = ticket
  var remote : $B.builder(0) = $B.create()
  val @(listed, _) = capture_with("git",
    $L.list_vt_cons(arg_text("git"), _git_in(a, name, $L.list_vt_cons(arg_text("ls-remote"), args3(arg_text("--heads"), arg_text("origin"), arg_range("refs/heads/adopt-", a, ks, ke, ""))))),
    no_arguments(), remote)
  val @(remote_array, remote_len) = $B.to_arr(remote)
  val () = $A.free<byte>(remote_array)
in
  if listed != 0 then _fail(a, name, "git ls-remote", listed)
  else if remote_len > 0 then _resume(a, name, ticket, template, target, is_issue, commit, comment)
  else let
    val checked = run_program("git", _git_in(a, name, $L.list_vt_cons(arg_text("checkout"), args3(arg_text("--quiet"), arg_text("-b"), arg_range("adopt-", a, ks, ke, "")))))
  in
    if checked != 0 then _fail(a, name, "git checkout", checked)
    else let
      val added = run_program("git", _git_in(a, name, $L.list_vt_cons(arg_text("add"), args2(arg_text("--"), _relative_arg(a, target, is_issue)))))
    in
      if added != 0 then _fail(a, name, "git add", added)
      else let
        val committed = run_program("git", _git_in(a, name, $L.list_vt_cons(arg_text("commit"), args3(arg_text("--quiet"), arg_text("-m"), _title_arg(a, template, commit)))))
      in
        if committed != 0 then _fail(a, name, "git commit", committed)
        else _open(a, name, ticket, template, target, is_issue, commit, comment, "HEAD", true)
      end
    end
  end
end

(* One repository: cloned, the file written and compared with the one it has, then published; 1 when it was refused or failed *)
fn _one {a_l,t_l:agz}{n:pos | n <= 4096}{tlen:nat | tlen <= 524288}
  (a: !$A.borrow(byte, a_l, n), name: range(n), ticket: range(n), template: range(n), target: range(n), is_issue: bool, commit: range(n), comment: range(n),
   t: !$A.borrow(byte, t_l, 524288), tlen: int tlen, show: bool): int = let
  val @(ns, ne) = name
  val @(cs, ce) = commit
  val @(ms, me) = comment
  val _ = run_program("rm", args3(arg_text("-rf"), arg_text("--"), _clone_arg(a, name, "")))
  val cloned = run_program("git",
    $L.list_vt_cons(arg_text("clone"), $L.list_vt_cons(arg_text("--quiet"), $L.list_vt_cons(arg_text("--depth"), $L.list_vt_cons(arg_text("1"),
    $L.list_vt_cons(arg_text("--"), $L.list_vt_cons(arg_range("https://github.com/bats-lang/", a, ns, ne, ".git"),
    $L.list_vt_cons(_clone_arg(a, name, ""), $L.list_vt_nil()))))))))
in
  if cloned != 0 then _fail(a, name, "git clone", cloned)
  else let
    (* the file the repository has, if any *)
    val @(target_array, target_len) = _target_path(a, name, target, is_issue)
    val @(target_frozen, target_view) = $A.freeze<byte>(target_array)
    var existing : $B.builder(0) = $B.create()
    val @(existing_ended, _) = read_file(target_view, target_len, existing)
    val () = $A.drop<byte>(target_frozen, target_view)
    val () = $A.free<byte>($A.thaw<byte>(target_frozen))
    val @(existing_array, existing_len) = $B.to_arr(existing)
    val @(existing_frozen, existing_view) = $A.freeze<byte>(existing_array)
    (* the template filled, written over it, and read back *)
    val _ = run_program("mkdir", args3(arg_text("-p"), arg_text("--"), _directory_arg(a, name, is_issue)))
    val existing_whole = (case+ existing_ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
    val has_hole = (_hole_at(t, tlen, 0) >= 0): bool
    val @(minute_start, minute_count, minute_valid) = _minute_of(t, tlen, existing_view, existing_len, existing_whole)
    var rope : $B.sized_rope = $B.sized_rope_create()
    val () = _fill(t, tlen, 0, rope, a, cs, ce, ms, me, existing_view, minute_start, minute_start + minute_count, ~minute_valid)
    val written = write_rope(_target_path(a, name, target, is_issue), rope)
    val @(back_array, back_len) = _target_path(a, name, target, is_issue)
    val @(back_frozen, back_view) = $A.freeze<byte>(back_array)
    var again : $B.builder(0) = $B.create()
    val @(again_ended, _) = read_file(back_view, back_len, again)
    val () = $A.drop<byte>(back_frozen, back_view)
    val () = $A.free<byte>($A.thaw<byte>(back_frozen))
    val @(again_array, again_len) = $B.to_arr(again)
    val @(again_frozen, again_view) = $A.freeze<byte>(again_array)
    val again_whole = (case+ again_ended of | Read_whole() => true | Read_too_long() => false | Read_failed() => false): bool
    (* the first byte where the two differ: ~1 none, ~2 the file is too long to read, ~3 there was none *)
    val differs =
      (case+ existing_ended of
       | Read_whole() => _differ(existing_view, existing_len, again_view, again_len, 0)
       | Read_too_long() => ~2
       | Read_failed() => ~3): int
    val result =
      (if ~written then _fail(a, name, "writing the file", 0)
       else if ~again_whole then _fail(a, name, "reading the file back", 0)
       else if differs = ~1 then let
         val () = _line(a, name)
         val () = print! ("- - no-op: ")
         val () = _print_path(a, target, is_issue)
       in (println! (" is already the template with its holes filled"); 0) end
       else if differs = ~2 then let
         val () = _line(a, name)
         val () = print! ("- - refused: ")
         val () = _print_path(a, target, is_issue)
       in (println! (" is longer than 524288 bytes"); 1) end
       else if differs >= 0 && ~(has_hole && minute_count > 0) then let
         val () = _line(a, name)
         val () = print! ("- - refused: ")
         val () = _print_path(a, target, is_issue)
       in (println! (" differs from the template with its holes filled at byte ", differs + 1); 1) end
       else let
         val () = if has_hole then let
             val () = _line(a, name)
             val () = print! ("minute ")
           in
             if minute_valid then let
               val () = print_range(existing_view, minute_start, minute_start + minute_count)
             in println! (", the minute of the cron line of the file it replaces") end
             else if minute_count > 0 then println! ("17, the default: the cron line of the file it replaces has no minute from 0 to 59")
             else println!("17, the default: the repository has no such cron line")
           end
           else ()
         val () = if show then let
             val () = _line(a, name)
             val () = print! ("wrote ")
             val () = _print_path(a, target, is_issue)
             val () = println! (":")
           in print_range(again_view, 0, again_len) end
           else ()
       in _publish(a, name, ticket, template, target, is_issue, commit, comment) end): int
    val () = $A.drop<byte>(again_frozen, again_view)
    val () = $A.free<byte>($A.thaw<byte>(again_frozen))
    val () = $A.drop<byte>(existing_frozen, existing_view)
    val () = $A.free<byte>($A.thaw<byte>(existing_frozen))
  in result end
end

(* The entries from at, each adopted (or those named only); the failures counted *)
fun _each {a_l,t_l:agz}{n:pos | n <= 4096}{len:nat | len <= n}{tlen:nat | tlen <= 524288}{at:nat | at <= len} .<len - at>.
  (a: !$A.borrow(byte, a_l, n), len: int len, at: int at, has_only: bool, only: range(n),
   template: range(n), target: range(n), is_issue: bool, commit: range(n), comment: range(n),
   t: !$A.borrow(byte, t_l, 524288), tlen: int tlen, failures: int): int =
  if at >= len then failures
  else let
    val @(ok, name, ticket, next) = _entry(a, len, at)
    val status =
      (if ok && (~has_only || _same(a, name, only)) then _one(a, name, ticket, template, target, is_issue, commit, comment, t, tlen, has_only)
       else 0): int
  in _each(a, len, next, has_only, only, template, target, is_issue, commit, comment, t, tlen, (if status != 0 then failures + 1 else failures)) end

(* ============================================================
   The run
   ============================================================ *)

#pub fn adopt_run (): int

(* The status: 0 when every repository adopted is left alone or has its pull request, 1 when one is refused or failed,
   2 for arguments that are not `[--only NAME] TEMPLATE COMMIT COMMENT NAME#TICKET...` *)
implement adopt_run () = let
  val arguments = $A.alloc<byte>(4096)
  val [len:int] len = (case+ $E.args_read(arguments, 4096) of | ~$R.some(count) => count | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(frozen, view) = $A.freeze<byte>(arguments)
  val first = _after_program(view, len)
  val first_stop = _arg_stop(view, len, first)
  val has_only = line_is(view, first, first_stop, "--only")
  val after_flag = (if has_only then _arg_next(view, len, first) else first): [p:nat | p <= len] int p
  val @(only_ok, only, after_only) =
    (if has_only then _take(view, len, after_flag) else @(true, @(0, 0), after_flag)): @(bool, range(4096), [p:nat | p <= len] int p)
  val as_stop = _arg_stop(view, len, after_only)
  val has_as = line_is(view, after_only, as_stop, "--as")
  val after_as_flag = (if has_as then _arg_next(view, len, after_only) else after_only): [p:nat | p <= len] int p
  val @(as_ok, as_file, after_as) =
    (if has_as then _take(view, len, after_as_flag) else @(true, @(0, 0), after_as_flag)): @(bool, range(4096), [p:nat | p <= len] int p)
  val @(template_ok, template, after_template) = _take(view, len, after_as)
  val target = (if has_as then as_file else template): range(4096)
  val @(target_start, target_stop) = target
  val target_ok = as_ok && class_end(view, target_stop, target_start, Class_name()) = target_stop: bool
  val @(commit_ok, commit, after_commit) = _take(view, len, after_template)
  val @(comment_ok, comment, after_comment) = _take(view, len, after_commit)
  val @(kind_ok, is_issue) = _template_kind(view, template)
  val surveyed = _survey(view, len, after_comment, has_only, only, 0)
  val usable = only_ok && (~has_as || target_ok) && template_ok && commit_ok && comment_ok && kind_ok && _is_commit(view, commit) && _is_comment(view, comment) && surveyed > 0: bool
  val status =
    (if ~usable then let
       val () = println! ("usage: adopt [--only NAME] [--as FILE] TEMPLATE COMMIT COMMENT NAME#TICKET...")
       val () = println! ("  TEMPLATE a file of tools/pin-audit/templates (or ISSUE_TEMPLATE/<file>), COMMIT 40 lowercase hex digits, COMMENT the pin's version comment,")
       val () = println! ("  each NAME#TICKET a repository of bats-lang and the ticket that asks it to adopt the template; --only NAME must be one of them;")
       val () = println! ("  --as FILE the name in .github/workflows the template is written as (relock-regenerate.yml as relock.yml), the template's own name by default")
     in 2 end
     else let
       val @(template_array, template_len) = _template_path(view, template)
       val @(template_frozen, template_view) = $A.freeze<byte>(template_array)
       var text : $B.builder(0) = $B.create()
       val @(ended, why) = read_file(template_view, template_len, text)
       val () = $A.drop<byte>(template_frozen, template_view)
       val () = $A.free<byte>($A.thaw<byte>(template_frozen))
       val @(text_array, text_len) = $B.to_arr(text)
       val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
       val result =
         (case+ ended of
          | Read_whole() => (if _each(view, len, after_comment, has_only, only, template, target, is_issue, commit, comment, text_view, text_len, 0) > 0 then 1 else 0)
          | Read_too_long() => let
              val () = println! ("adopt: the template is longer than the 524288 bytes adopt reads")
            in 1 end
          | Read_failed() => let
              val () = println! ("adopt: the template could not be read (run adopt at the root of a checkout of repository-prototype): ", why)
            in 1 end): int
       val () = $A.drop<byte>(text_frozen, text_view)
       val () = $A.free<byte>($A.thaw<byte>(text_frozen))
     in result end): int
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in status end
