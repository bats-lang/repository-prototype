(* pin_audit -- the weekly audit of the organisation's CI pins
   (bats-lang/repository-prototype#365, piece 3 of #353; the audit #352 was).

   pin-audit

   1. The non-archived repositories of the organisation: `gh api --paginate
      orgs/bats-lang/repos`, its own jq keeping the names of those with
      archived false. Bats has no HTTP client (no package of the
      repository makes a request; bridge's fetch is the browser's), so the
      list is the GitHub CLI's, which the runner image ships and which
      reads the job's GH_TOKEN. A failed gh, or a list longer than the
      buffer that holds it, fails the run with a message of its own: an
      audit that saw part of the organisation says so.
   2. For each name, a shallow clone into audit-clones/<name> (git, one
      request for all of a repository's files, and the checker's own file
      discovery then reads them as it reads a checkout).
   3. Every workflow file of the clone (.github/workflows/*.yml and *.yaml)
      is in the allowlist, tools/pin-audit/allowlist.txt, in exact text.
      The audit never reads YAML: it compares bytes with text it was told is
      fine, and rejects everything else as "not in the allowlist". A file is
      accepted in one of three ways, and in no other:
        a. its sha256 is listed with its repository and path (kind file):
           the review gates, which run no bats and are copied whole;
        b. it is a caller of a shared workflow, with no job of its own: every
           line is blank, a comment, a line indented under six spaces that
           the allowlist knows (a key, a name, a whole line), or a deeper
           line that is an entry of kind caller;
        c. it runs jobs, and its lines indented under six spaces are all
           known as in b, and a line "    steps:" is followed by the
           checkout step (kind prologue), then the setup step in its
           canonical lines, "- name: Set up bats", an id, "uses:
           bats-lang/bats/.github/actions/setup@<40 hex>" (in the
           repository bats alone, ./.github/actions/setup too) and its
           with lines (kinds setup-name, setup-id, setup-uses,
           setup-uses-bats, setup-with, setup-input), and then the next
           step. A step that is conditional or whose failure is ignored has
           no such spelling.
      A correct workflow written another way fails, and is rewritten.
      Carriage returns anywhere fail a file. The setup action is what runs
      the pin check, so a workflow that does not call it skips it.
   4. The checker itself: `bats check-pins --discover` inside the clone
      (env -C), its findings and the exceptions it lists
      (`# unpinned: <reason>`, listed and not failures) in the job log.

   Every file's result is a line of the log (pass, and how, or a ::error
   line naming the repository, the workflow and why); the run ends with a
   summary line and the failing repositories and a status of 1, so the run
   is red and says which. Nothing in the clones is run: only read.

   Bounds are in the types. A buffer is read at an index the types prove in
   range; an argument is built from a builder whose length the types prove
   fits; a text that does not fit its buffer (the list of repositories, the
   list of workflows, a workflow) is the outcome `Drained_too_long`, which
   every caller matches with case+ and answers with an error and a failed
   run; the names of the failing repositories are a rope, which has no
   bound. Nothing is dropped and nothing ends early without saying so.

   The program is bats because we write bats (quire#646); the tools it calls
   (gh, git, cat, sha256sum, env -C of GNU coreutils, bats) are the runner's
   and the pinned compiler's. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use list as L
#use process as P
#use result as R

(* How reading a pipe ended: it all fit, it did not fit the buffer, or a
   read failed. Every caller matches all three (case+). *)
datatype drained =
  | Drained_whole
  | Drained_too_long
  | Drained_failed

(* The most bytes a repository's name or a workflow's path may have is 255
   (GitHub allows 100 for a repository, and 255 is a file name's limit), so
   a longer one is not a name the audit will put in an argument; it is
   reported, not cut. *)

(* ============================================================
   Arguments
   ============================================================ *)

(* b[i, k) appended to out; the builder's length after is in its type, and
   the caller proves it fits *)
fun _put_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{m:nat | m + (k - i) <= 524288} .<k - i>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int k,
   out: !$B.builder(m) >> $B.builder(m + (k - i))): void =
  if i >= k then ()
  else let
    val () = $B.put_char(out, $AR.low_byte(byte2int0($A.read<byte>(b, i))))
  in _put_range(b, i + 1, k, out) end

(* b[i, k) to stdout *)
fun _print_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n} .<k - i>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int k): void =
  if i >= k then ()
  else let
    val () = print_char(int2char0(byte2int0($A.read<byte>(b, i))))
  in _print_range(b, i + 1, k) end

fn _arg_s {sn:nat | sn <= 524288} (s: string sn): $P.arg_entry = let
  var b : $B.builder(0) = $B.create()
  val () = $B.bput(b, s)
  val @(a, k) = $B.to_arr(b)
in @(a, k) end

(* leading text, then the name b[s, e), then trailing text, as one argument *)
fn _arg_name {l:agz}{s,e:nat | s <= e; e <= 524288} {pn,sn:nat | pn + (e - s) + sn <= 524288}
  (leading: string pn, b: !$A.borrow(byte, l, 524288), s: int s, e: int e, trailing: string sn): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, leading)
  val () = _put_range(b, s, e, out)
  val () = $B.bput(out, trailing)
  val @(a, k) = $B.to_arr(out)
in @(a, k) end

(* ============================================================
   Running a program
   ============================================================ *)

(* A program on PATH with its arguments, the output and the errors shared
   with this process: its exit status, or ~1 when it could not be run *)
fn _run {pn:nat | pn < 524288}
  (program: string pn, argv: $L.listv($P.arg_entry)): int = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(fz, bv) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_proved(nul | bv, argv, $P.inherit(), $P.inherit(), $P.inherit())
  val () = $A.cborrow_drop(fz, bv)
  val () = $A.barr_free($A.barr_thaw(fz))
in
  case+ spawned of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val () = $P.pipe_end_close(serr_p)
    in case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1 end
  | ~$R.err(_) => ~1
end

(* Reads a pipe to its end into out. A chunk that would take the builder
   past its capacity is not appended (nothing is cut): the outcome is
   Drained_too_long. Each chunk is at least one byte, so the room left is
   the metric. *)
fun _drain {m:nat | m <= 524288} .<524288 - m>.
  (fd: !$F.fd, out: !$B.builder(m) >> $B.builder_v): drained = let
  val chunk = $A.alloc<byte>(4096)
in
  case+ $F.file_read(fd, chunk, 4096) of
  | ~$R.err(_) => let val () = $A.free<byte>(chunk) in Drained_failed() end
  | ~$R.ok(k) =>
    if k <= 0 then let val () = $A.free<byte>(chunk) in Drained_whole() end
    else if $B.length(out) + k > 524288 then let val () = $A.free<byte>(chunk) in Drained_too_long() end
    else let
      val @(fz, bv) = $A.freeze<byte>(chunk)
      val () = _put_range(bv, 0, k, out)
      val () = $A.drop<byte>(fz, bv)
      val () = $A.free<byte>($A.thaw<byte>(fz))
    in _drain(fd, out) end
end

(* A program on PATH with its arguments, its standard output read into out
   (its errors shared with this process): its exit status (~1 when it could
   not be run) and how the reading ended *)
fn _capture {pn:nat | pn < 524288}
  (program: string pn, argv: $L.listv($P.arg_entry),
   out: !$B.builder(0) >> $B.builder_v): @(int, drained) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(fz, bv) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_proved(nul | bv, argv, $P.inherit(), $P.pipe_new(), $P.inherit())
  val () = $A.cborrow_drop(fz, bv)
  val () = $A.barr_free($A.barr_thaw(fz))
in
  case+ spawned of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(serr_p)
      val+ ~$P.pipe_fd(out_fd) = sout_p
      val read_end = _drain(out_fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(out_fd))
      val status = (case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in @(status, read_end) end
  | ~$R.err(_) => @(~1, Drained_whole())
end

(* ============================================================
   Lines of a buffer
   ============================================================ *)

(* The end of the line that starts at i: the place of its newline, or k *)
fun _line_end {l:agz}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if byte2int0($A.read<byte>(b, i)) = 10 then i
  else _line_end(b, k, i + 1)

(* ============================================================
   The allowlist: exact text, compared byte by byte
   ============================================================ *)

(* The allowlist is tools/pin-audit/allowlist.txt, read once (its entries are
   one on each line: a kind, a colon, then the text; the file explains the
   kinds). Nothing here reads YAML: a line is compared with an entry byte by
   byte, and the entry's text is exact except for three marks, a backquote
   and a letter: `H is forty lowercase hexadecimal digits, `N is one or two
   digits, and `C (at the end of an entry) is nothing or " # " and any text.
   Keyword: allowlist (the research and the cases are on #365). *)

(* Whether b[i, k) starts with the text s from its m-th character on *)
fun _lit_from {l:agz}{k:nat | k <= 524288}{i:nat | i <= k}{sl:nat}{m:nat | m <= sl} .<sl - m>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i, s: string sl, sl: int sl, m: int m): bool =
  if m >= sl then true
  else if i >= k then false
  else if byte2int0($A.read<byte>(b, i)) = char2int0(string_get_at(s, m)) then _lit_from(b, k, i + 1, s, sl, m + 1)
  else false

(* Whether the line b[ls, le) is exactly the text s *)
fn _lit_eq {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}{sl:nat}
  (b: !$A.borrow(byte, l, 524288), le: int le, ls: int ls, s: string sl): bool = let
  val sl = g1u2i(string1_length(s))
in
  if le - ls = sl then _lit_from(b, le, ls, s, sl, 0) else false
end

(* The place after the spaces that begin b[i, k) *)
fun _skip_spaces {l:agz}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if byte2int0($A.read<byte>(b, i)) = 32 then _skip_spaces(b, k, i + 1)
  else i

(* Whether the line b[ls, le) is blank or a comment: its first character
   that is not a space is the end, or a '#' *)
fn _ignorable {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (b: !$A.borrow(byte, l, 524288), le: int le, ls: int ls): bool = let
  val first = _skip_spaces(b, le, ls)
in
  if first >= le then true else byte2int0($A.read<byte>(b, first)) = 35
end

(* Whether n lowercase hexadecimal digits are at b[i, k) *)
fun _hex_run {l:agz}{k:nat | k <= 524288}{i:nat | i <= k}{n:nat} .<n>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i, n: int n): bool =
  if n <= 0 then true
  else if i >= k then false
  else let
    val c = byte2int0($A.read<byte>(b, i))
  in
    if (c >= 48 && c <= 57) || (c >= 97 && c <= 102) then _hex_run(b, k, i + 1, n - 1) else false
  end

(* How many digits (at most two) are at b[i, k) *)
fn _digits_upto_two {l:agz}{k:nat | k <= 524288}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i): [c:nat | c <= 2; i + c <= k] int c =
  if i >= k then 0
  else let
    val first = byte2int0($A.read<byte>(b, i))
  in
    if first >= 48 && first <= 57 then
      (if i + 1 >= k then 1
       else let val second = byte2int0($A.read<byte>(b, i + 1)) in
         if second >= 48 && second <= 57 then 2 else 1 end)
    else 0
  end

(* Whether the line fb[j, le) is what the entry ab[i, ee) says, from i and j
   on: its bytes, with the three marks above *)
fun _match_at {l,l2:agz}{ee:nat | ee <= 524288}{le:nat | le <= 524288}{i:nat | i <= ee}{j:nat | j <= le} .<ee - i>.
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, i: int i,
   fb: !$A.borrow(byte, l2, 524288), le: int le, j: int j): bool =
  if i >= ee then j >= le
  else let
    val c = byte2int0($A.read<byte>(ab, i))
  in
    if c = 96 then
      (if i + 1 >= ee then false
       else let
         val mark = byte2int0($A.read<byte>(ab, i + 1))
       in
         if mark = 72 then
           (if j + 40 <= le then
              (if _hex_run(fb, le, j, 40) then _match_at(ab, ee, i + 2, fb, le, j + 40) else false)
            else false)
         else if mark = 78 then let
           val digits = _digits_upto_two(fb, le, j)
         in
           if digits >= 1 then _match_at(ab, ee, i + 2, fb, le, j + digits) else false
         end
         else if mark = 67 then
           (if i + 2 = ee then
              (if j >= le then true
               else if j + 3 <= le then _lit_from(fb, le, j, " # ", 3, 0)
               else false)
            else false)
         else false
       end)
    else if j >= le then false
    else if byte2int0($A.read<byte>(fb, j)) = c then _match_at(ab, ee, i + 1, fb, le, j + 1)
    else false
  end

(* Whether some entry of the kind, one on each line of ab[i, an), is the
   line fb[ls, le) *)
fun _entry_any {l,l2:agz}{an:nat | an <= 524288}{le:nat | le <= 524288}{ls:nat | ls <= le}{i:nat | i <= an}{sk:nat} .<an - i>.
  (ab: !$A.borrow(byte, l, 524288), an: int an, i: int i, kind: string sk,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): bool = let
  val ae = _line_end(ab, an, i)
  val kind_len = g1u2i(string1_length(kind))
  val here =
    (if i + kind_len < ae then
       (if _lit_from(ab, ae, i, kind, kind_len, 0) then
          (if byte2int0($A.read<byte>(ab, i + kind_len)) = 58 then _match_at(ab, ae, i + kind_len + 1, fb, le, ls)
           else false)
        else false)
     else false): bool
in
  if here then true
  else if ae >= an then false
  else _entry_any(ab, an, ae + 1, kind, fb, le, ls)
end

(* Whether the entry text ab[i, ee) is a prefix of the line fb[j, le) *)
fun _prefix_eq {l,l2:agz}{ee:nat | ee <= 524288}{le:nat | le <= 524288}{i:nat | i <= ee}{j:nat | j <= le} .<ee - i>.
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, i: int i,
   fb: !$A.borrow(byte, l2, 524288), le: int le, j: int j): bool =
  if i >= ee then true
  else if j >= le then false
  else if byte2int0($A.read<byte>(ab, i)) = byte2int0($A.read<byte>(fb, j)) then _prefix_eq(ab, ee, i + 1, fb, le, j + 1)
  else false

(* A character a value may hold: letters, digits and . , / - : @ ( ) = + * $ _ *)
fn _plain_char (c: int): bool =
  (c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57)
  || c = 46 || c = 44 || c = 47 || c = 45 || c = 58 || c = 64 || c = 40 || c = 41
  || c = 61 || c = 43 || c = 42 || c = 36 || c = 95

(* Whether fb[i, le) is a value text of a key line: only the characters of
   _plain_char, spaces, quotes in pairs and brackets and braces in balance,
   up to a " #" that begins a comment (a value has no '|', '>', '&', '!',
   '\' or a quote left open, so it cannot start a block scalar or go on to
   the next line) *)
fun _value_ok {l:agz}{le:nat | le <= 524288}{i:nat | i <= le} .<le - i>.
  (fb: !$A.borrow(byte, l, 524288), le: int le, i: int i,
   square: int, brace: int, single: int, double: int): bool =
  if i >= le then (square = 0 && brace = 0 && single = 0 && double = 0)
  else let
    val c = byte2int0($A.read<byte>(fb, i))
  in
    if c = 32 then
      (if i + 1 < le then
         (if byte2int0($A.read<byte>(fb, i + 1)) = 35 then (square = 0 && brace = 0 && single = 0 && double = 0)
          else _value_ok(fb, le, i + 1, square, brace, single, double))
       else _value_ok(fb, le, i + 1, square, brace, single, double))
    else if c = 91 then _value_ok(fb, le, i + 1, square + 1, brace, single, double)
    else if c = 93 then (if square <= 0 then false else _value_ok(fb, le, i + 1, square - 1, brace, single, double))
    else if c = 123 then _value_ok(fb, le, i + 1, square, brace + 1, single, double)
    else if c = 125 then (if brace <= 0 then false else _value_ok(fb, le, i + 1, square, brace - 1, single, double))
    else if c = 39 then _value_ok(fb, le, i + 1, square, brace, 1 - single, double)
    else if c = 34 then _value_ok(fb, le, i + 1, square, brace, single, 1 - double)
    else if _plain_char(c) then _value_ok(fb, le, i + 1, square, brace, single, double)
    else false
  end

(* Whether the line fb[ls, le) is a key entry's text (the key and its colon,
   with the indentation) and then nothing, or a space and a value that is
   _value_ok *)
fn _key_line_ok {l,l2:agz}{ee:nat | ee <= 524288}{le:nat | le <= 524288}{es:nat | es <= ee}{ls:nat | ls <= le}
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, es: int es,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): bool =
  if ls + (ee - es) <= le then
    (if _prefix_eq(ab, ee, es, fb, le, ls) then let
       val after = ls + (ee - es)
     in
       if after >= le then true
       else if byte2int0($A.read<byte>(fb, after)) = 32 then _value_ok(fb, le, after + 1, 0, 0, 0, 0)
       else false
     end
     else false)
  else false

(* Whether some key entry of ab[i, an) is the line fb[ls, le) *)
fun _key_any {l,l2:agz}{an:nat | an <= 524288}{le:nat | le <= 524288}{ls:nat | ls <= le}{i:nat | i <= an} .<an - i>.
  (ab: !$A.borrow(byte, l, 524288), an: int an, i: int i,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): bool = let
  val ae = _line_end(ab, an, i)
  val here =
    (if i + 4 < ae then
       (if _lit_from(ab, ae, i, "key", 3, 0) then
          (if byte2int0($A.read<byte>(ab, i + 3)) = 58 then _key_line_ok(ab, ae, i + 4, fb, le, ls)
           else false)
        else false)
     else false): bool
in
  if here then true
  else if ae >= an then false
  else _key_any(ab, an, ae + 1, fb, le, ls)
end

(* The end of a run of identifier characters (letters, digits, '_', '-') *)
fun _id_run {l:agz}{le:nat | le <= 524288}{i:nat | i <= le} .<le - i>.
  (fb: !$A.borrow(byte, l, 524288), le: int le, i: int i): [j:nat | i <= j; j <= le] int j =
  if i >= le then i
  else let
    val c = byte2int0($A.read<byte>(fb, i))
  in
    if (c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57) || c = 95 || c = 45
    then _id_run(fb, le, i + 1)
    else i
  end

(* Whether the line fb[ls, le) is two spaces, a name and a colon, and nothing
   else: a job's name or an event's, whose value is on the lines below *)
fn _id_line {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (fb: !$A.borrow(byte, l, 524288), le: int le, ls: int ls): bool =
  if ls + 4 > le then false
  else if byte2int0($A.read<byte>(fb, ls)) = 32 then
    (if byte2int0($A.read<byte>(fb, ls + 1)) = 32 then let
       val name_end = _id_run(fb, le, ls + 2)
     in
       if name_end > ls + 2 then
         (if name_end + 1 = le then byte2int0($A.read<byte>(fb, name_end)) = 58 else false)
       else false
     end
     else false)
  else false

(* Whether the line fb[ls, le), indented under six spaces, is one the
   allowlist knows: a whole line (kind line), a name line, or a key (kind key) *)
fn _structure_ok {l,l2:agz}{an:nat | an <= 524288}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (ab: !$A.borrow(byte, l, 524288), an: int an,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): bool =
  if _entry_any(ab, an, 0, "line", fb, le, ls) then true
  else if _id_line(fb, le, ls) then true
  else _key_any(ab, an, 0, fb, le, ls)

(* ============================================================
   The lines of a workflow file
   ============================================================ *)

(* Whether the byte v is anywhere in b[i, k) *)
fun _has_byte {l:agz}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i, v: int): bool =
  if i >= k then false
  else if byte2int0($A.read<byte>(b, i)) = v then true
  else _has_byte(b, k, i + 1, v)

(* The number of the line that starts at p (the first is 1) *)
fun _line_no {l:agz}{k:nat | k <= 524288}{p:nat | p <= k}{i:nat | i <= p} .<p - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, p: int p, i: int i, n: int): int =
  if i >= p then n
  else if byte2int0($A.read<byte>(b, i)) = 10 then _line_no(b, k, p, i + 1, n + 1)
  else _line_no(b, k, p, i + 1, n)

(* The start of the first line indented under six spaces that is not blank,
   not a comment and not an allowed structure line; k when there is none *)
fun _structure_scan {l,l2:agz}{an:nat | an <= 524288}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (fb: !$A.borrow(byte, l, 524288), k: int k,
   ab: !$A.borrow(byte, l2, 524288), an: int an, i: int i): [p:nat | i <= p; p <= k] int p = let
  val e = _line_end(fb, k, i)
  val first = _skip_spaces(fb, e, i)
  val bad = (if _ignorable(fb, e, i) then false
             else if first - i >= 6 then false
             else ~_structure_ok(ab, an, fb, e, i)): bool
in
  if bad then i
  else if e >= k then k
  else _structure_scan(fb, k, ab, an, e + 1)
end

(* The start of the first line indented six spaces or more that is not blank,
   not a comment and not an entry of kind caller; k when there is none *)
fun _caller_scan {l,l2:agz}{an:nat | an <= 524288}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (fb: !$A.borrow(byte, l, 524288), k: int k,
   ab: !$A.borrow(byte, l2, 524288), an: int an, i: int i): [p:nat | i <= p; p <= k] int p = let
  val e = _line_end(fb, k, i)
  val first = _skip_spaces(fb, e, i)
  val bad = (if _ignorable(fb, e, i) then false
             else if first - i < 6 then false
             else ~_entry_any(ab, an, 0, "caller", fb, e, i)): bool
in
  if bad then i
  else if e >= k then k
  else _caller_scan(fb, k, ab, an, e + 1)
end

(* ============================================================
   The setup step: a fixed run of lines
   ============================================================ *)

(* The states of the scan for the canonical setup step:
   0 not after a steps line; 1 after the line "    steps:" and the lines the
   allowlist lets come before the setup step (kind prologue); 2 after the
   name line of the step; 3 after its id line; 4 after its uses line; 5 in
   its with lines; 9 the step is there and the next step, or a line of the
   job above its steps, has begun. A blank line or a comment changes no
   state. A line that is not what the state expects ends the run, and is
   itself looked at as the start of one (it may be "    steps:"). *)

(* 1 when the line is "    steps:", else 0 *)
fn _after_steps_line {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (fb: !$A.borrow(byte, l, 524288), le: int le, ls: int ls): int =
  if _lit_eq(fb, le, ls, "    steps:") then 1 else 0

(* 9 when the line begins the next step (six spaces, a dash and a space) or is
   indented under six spaces, else what the line starts *)
fn _step_ends {l:agz}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (fb: !$A.borrow(byte, l, 524288), le: int le, ls: int ls): int = let
  val first = _skip_spaces(fb, le, ls)
in
  if first - ls < 6 then 9
  else if _lit_from(fb, le, ls, "      - ", 8, 0) then 9
  else _after_steps_line(fb, le, ls)
end

(* Whether the line is the uses line of the setup step: bats's action at a
   full commit (kind setup-uses), and in the repository bats alone the action
   of its own path too (kind setup-uses-bats) *)
fn _uses_line {l,l2:agz}{an:nat | an <= 524288}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (ab: !$A.borrow(byte, l, 524288), an: int an, in_bats: bool,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): bool =
  if _entry_any(ab, an, 0, "setup-uses", fb, le, ls) then true
  else if in_bats then _entry_any(ab, an, 0, "setup-uses-bats", fb, le, ls)
  else false

fn _next_state {l,l2:agz}{an:nat | an <= 524288}{le:nat | le <= 524288}{ls:nat | ls <= le}
  (state: int, ab: !$A.borrow(byte, l, 524288), an: int an, in_bats: bool,
   fb: !$A.borrow(byte, l2, 524288), le: int le, ls: int ls): int =
  if state = 0 then _after_steps_line(fb, le, ls)
  else if state = 1 then
    (if _entry_any(ab, an, 0, "prologue", fb, le, ls) then 1
     else if _entry_any(ab, an, 0, "setup-name", fb, le, ls) then 2
     else _after_steps_line(fb, le, ls))
  else if state = 2 then
    (if _entry_any(ab, an, 0, "setup-id", fb, le, ls) then 3
     else if _uses_line(ab, an, in_bats, fb, le, ls) then 4
     else _after_steps_line(fb, le, ls))
  else if state = 3 then
    (if _uses_line(ab, an, in_bats, fb, le, ls) then 4
     else _after_steps_line(fb, le, ls))
  else if state = 4 then
    (if _entry_any(ab, an, 0, "setup-with", fb, le, ls) then 5
     else _step_ends(fb, le, ls))
  else
    (if _entry_any(ab, an, 0, "setup-input", fb, le, ls) then 5
     else _step_ends(fb, le, ls))

(* The state after the lines of fb[i, k): 9 as soon as it is reached *)
fun _setup_scan {l,l2:agz}{an:nat | an <= 524288}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (fb: !$A.borrow(byte, l, 524288), k: int k,
   ab: !$A.borrow(byte, l2, 524288), an: int an, in_bats: bool, state: int, i: int i): int = let
  val e = _line_end(fb, k, i)
  val state2 = (if _ignorable(fb, e, i) then state else _next_state(state, ab, an, in_bats, fb, e, i)): int
in
  if state2 = 9 then 9
  else if e >= k then state2
  else _setup_scan(fb, k, ab, an, in_bats, state2, e + 1)
end

(* ============================================================
   Files listed by their hash
   ============================================================ *)

(* Whether the entry ab[i, ee) holds the bytes xb[xs, xe) from p on *)
fun _range_eq {l,l2:agz}{ee:nat | ee <= 524288}{xe:nat | xe <= 524288}{i:nat | i <= ee}{xs:nat | xs <= xe} .<xe - xs>.
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, i: int i,
   xb: !$A.borrow(byte, l2, 524288), xs: int xs, xe: int xe): bool =
  if xs >= xe then true
  else if i >= ee then false
  else if byte2int0($A.read<byte>(ab, i)) = byte2int0($A.read<byte>(xb, xs)) then _range_eq(ab, ee, i + 1, xb, xs + 1, xe)
  else false

(* The place after xb[xs, xe) in the entry ab[.., ee) when it is there at p, else ~1 *)
fn _step_range {l,l2:agz}{ee:nat | ee <= 524288}{xe:nat | xe <= 524288}{xs:nat | xs <= xe}{p:int}
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, p: int p,
   xb: !$A.borrow(byte, l2, 524288), xs: int xs, xe: int xe): [r:int | r < 0 || r <= ee] int r =
  if p < 0 then ~1
  else if p + (xe - xs) <= ee then
    (if _range_eq(ab, ee, p, xb, xs, xe) then p + (xe - xs) else ~1)
  else ~1

(* The place after the text s in the entry ab[.., ee) when it is there at p, else ~1 *)
fn _step_text {l:agz}{ee:nat | ee <= 524288}{p:int}{sl:nat}
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, p: int p, s: string sl): [r:int | r < 0 || r <= ee] int r = let
  val sl = g1u2i(string1_length(s))
in
  if p < 0 then ~1
  else if p + sl <= ee then
    (if _lit_from(ab, ee, p, s, sl, 0) then p + sl else ~1)
  else ~1
end

(* Whether the entry text at t is the hash hb[0, 64), two spaces, the
   repository name b[s, e), a slash, the path pb[fs, fe) and two spaces *)
fn _file_entry_ok {l,l2,l3,l4:agz}{ee:nat | ee <= 524288}{t:int}{hk:nat | 64 <= hk; hk <= 524288}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288}
  (ab: !$A.borrow(byte, l, 524288), ee: int ee, t: int t,
   hb: !$A.borrow(byte, l2, 524288), hk: int hk,
   b: !$A.borrow(byte, l3, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l4, 524288), fs: int fs, fe: int fe): bool = let
  val p1 = _step_range(ab, ee, t, hb, 0, 64)
  val p2 = _step_text(ab, ee, p1, "  ")
  val p3 = _step_range(ab, ee, p2, b, s, e)
  val p4 = _step_text(ab, ee, p3, "/")
  val p5 = _step_range(ab, ee, p4, pb, fs, fe)
  val p6 = _step_text(ab, ee, p5, "  ")
in p6 >= 0 end

(* The start of the entry (kind file) in ab[i, an) that lists this file by
   its hash, else ~1 *)
fun _file_listed {l,l2,l3,l4:agz}{an:nat | an <= 524288}{i:nat | i <= an}{hk:nat | 64 <= hk; hk <= 524288}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288} .<an - i>.
  (ab: !$A.borrow(byte, l, 524288), an: int an, i: int i,
   hb: !$A.borrow(byte, l2, 524288), hk: int hk,
   b: !$A.borrow(byte, l3, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l4, 524288), fs: int fs, fe: int fe): [r:int | r < 0 || (0 <= r && r <= an)] int r = let
  val ae = _line_end(ab, an, i)
  val here =
    (if i + 5 < ae then
       (if _lit_from(ab, ae, i, "file:", 5, 0) then _file_entry_ok(ab, ae, i + 5, hb, hk, b, s, e, pb, fs, fe)
        else false)
     else false): bool
in
  if here then i
  else if ae >= an then ~1
  else _file_listed(ab, an, ae + 1, hb, hk, b, s, e, pb, fs, fe)
end

(* ============================================================
   2 to 4. One repository
   ============================================================ *)

(* Whether b[i, e) is a name GitHub gives a repository and the clone's path
   can hold: letters, digits, '.', '_' and '-', with a character that is
   not '.' (so never "." or ".."). The name goes into arguments, never a
   shell, and into audit-clones/<name>; nothing else may. *)
fun _name_ok {l:agz}{i,e:nat | i <= e; e <= 524288} .<e - i>.
  (b: !$A.borrow(byte, l, 524288), i: int i, e: int e, plain: bool): bool =
  if i >= e then plain
  else let
    val c = byte2int0($A.read<byte>(b, i))
    val letter = (c >= 97 && c <= 122) || (c >= 65 && c <= 90): bool
    val digit = c >= 48 && c <= 57: bool
    val dot = c = 46: bool
    val mark = c = 95 || c = 45: bool
  in
    if letter || digit || mark then _name_ok(b, i + 1, e, true)
    else if dot then _name_ok(b, i + 1, e, plain)
    else false
  end

(* The command line of the clone of b[s, e) *)
fn _clone_argv {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("clone"),
  $L.list_vt_cons(_arg_s("--quiet"),
  $L.list_vt_cons(_arg_s("--depth"),
  $L.list_vt_cons(_arg_s("1"),
  $L.list_vt_cons(_arg_name("https://github.com/bats-lang/", b, s, e, ".git"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
    $L.list_vt_nil())))))))

(* audit-clones/<name>/<path>, as one argument *)
fn _arg_path {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288; fe - fs <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): $P.arg_entry = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, "audit-clones/")
  val () = _put_range(b, s, e, out)
  val () = $B.bput(out, "/")
  val () = _put_range(pb, fs, fe, out)
  val @(a, k) = $B.to_arr(out)
in @(a, k) end

(* The tracked workflow files of the clone (.github/workflows/*.yml and
   *.yaml), one path on each line *)
fn _workflows_argv {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("ls-files"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yml"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yaml"),
    $L.list_vt_nil())))))))

(* The bytes of one workflow file *)
fn _cat_argv {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288; fe - fs <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("cat"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_path(b, s, e, pb, fs, fe),
    $L.list_vt_nil())))

(* The sha256 of one workflow file *)
fn _sum_argv {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288; fe - fs <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("sha256sum"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_path(b, s, e, pb, fs, fe),
    $L.list_vt_nil())))

(* Whether the repository b[s, e) is bats itself: the local path
   ./.github/actions/setup is bats's setup action there and that
   repository's own action in any other *)
fn _is_bats {l:agz}{s,e:nat | s <= e; e <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): bool =
  if e - s = 4 then
    (if byte2int0($A.read<byte>(b, s)) = 98 then
      (if byte2int0($A.read<byte>(b, s + 1)) = 97 then
        (if byte2int0($A.read<byte>(b, s + 2)) = 116 then byte2int0($A.read<byte>(b, s + 3)) = 115
        else false)
      else false)
    else false)
  else false

(* The checker, run inside the clone *)
fn _check_argv {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("env"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("bats"),
  $L.list_vt_cons(_arg_s("check-pins"),
  $L.list_vt_cons(_arg_s("--discover"),
    $L.list_vt_nil()))))))

(* The repository's name: a header for its part of the log *)
fn _header {l:agz}{s,e:nat | s <= e; e <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): void = let
  val () = print! ("== ")
  val () = _print_range(b, s, e)
in println! () end

(* The name b[s, e) appended to the list of the failing: a rope, which has
   no bound, so a name of any length is kept whole *)
fn _fail {l:agz}{s,e:nat | s <= e; e <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e, failing: !$B.sized_rope): void = let
  val () = $B.sized_rope_put(failing, 32)
in $B.sized_rope_copy(failing, b, s, e) end

(* The annotation that names the repository, ready for its message *)
fn _error_line {l:agz}{s,e:nat | s <= e; e <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): void = let
  val () = print! ("::error title=pin audit::")
  val () = _print_range(b, s, e)
in print! (": ") end

(* The start of a rejected file's message: the annotation, the workflow *)
fn _rejected_head {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): void = let
  val () = _error_line(b, s, e)
  val () = print! ("workflow ")
  val () = _print_range(pb, fs, fe)
in print! (" is not in the allowlist: ") end

(* What to do about a rejected file, said the same way for every reason *)
val _how_to_fix = "; rewrite it to the canonical form, or the allowlist (tools/pin-audit/allowlist.txt) gains the exact text through a reviewed pull request in repository-prototype"

(* The line that starts at p of cb[0, ck), as its number and its text *)
fn _show_line {l:agz}{ck:nat | ck <= 524288}{p:nat | p <= ck}
  (cb: !$A.borrow(byte, l, 524288), ck: int ck, p: int p): void = let
  val () = print! ("line ", _line_no(cb, ck, p, 0, 1), " (`")
  val () = _print_range(cb, p, _line_end(cb, ck, p))
in print! ("`)") end

(* The kind a workflow file turned out to be. Every caller matches all four
   (case+). *)
datatype kind =
  | Kind_listed
  | Kind_caller
  | Kind_runner
  | Kind_rejected

(* The counts over a repository or the whole run: workflow files, those
   listed by their hash, callers of a shared workflow, files that run jobs
   and call the setup action, and those rejected *)
typedef tally = @(int, int, int, int, int)

fn _count (t: tally, k: kind): tally = let
  val @(files, listed, callers, runners, rejected) = t
in
  case+ k of
  | Kind_listed() => @(files + 1, listed + 1, callers, runners, rejected)
  | Kind_caller() => @(files + 1, listed, callers + 1, runners, rejected)
  | Kind_runner() => @(files + 1, listed, callers, runners + 1, rejected)
  | Kind_rejected() => @(files + 1, listed, callers, runners, rejected + 1)
end

(* The start of the entry that lists the file by its hash, else ~1; ~1 too
   when sha256sum did not give a hash *)
fn _listed_at {l,l2,l3,l4:agz}{an:nat | an <= 524288}{hk:nat | hk <= 524288}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288}
  (ab: !$A.borrow(byte, l, 524288), an: int an,
   hb: !$A.borrow(byte, l2, 524288), hk: int hk, hashed: bool,
   b: !$A.borrow(byte, l3, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l4, 524288), fs: int fs, fe: int fe): [r:int | r < 0 || (0 <= r && r <= an)] int r =
  if hashed then
    (if hk >= 64 then _file_listed(ab, an, 0, hb, hk, b, s, e, pb, fs, fe) else ~1)
  else ~1

(* The kind of the workflow file pb[fs, fe) of the repository b[s, e), whose
   bytes are cb[0, ck) and the output of sha256sum on it hb[0, hk) (when it
   ran): the rule, one test for each kind of file, the first that holds. The
   line of the result is printed here. *)
fn _classify {l,l2,lc,lh,la:agz}{s,e,fs,fe,ck,hk,an:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288; fe - fs <= 255; ck <= 524288; hk <= 524288; an <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe,
   cb: !$A.borrow(byte, lc, 524288), ck: int ck,
   hb: !$A.borrow(byte, lh, 524288), hk: int hk, hashed: bool,
   ab: !$A.borrow(byte, la, 524288), an: int an): kind = let
  val listed_at = _listed_at(ab, an, hb, hk, hashed, b, s, e, pb, fs, fe)
in
  if listed_at >= 0 then let
    val () = print! ("   ")
    val () = _print_range(pb, fs, fe)
    val () = println! (": pass, a file the allowlist lists by its hash (allowlist.txt line ", _line_no(ab, an, listed_at, 0, 1), ")")
  in Kind_listed() end
  else if _has_byte(cb, ck, 0, 13) then let
    val () = _rejected_head(b, s, e, pb, fs, fe)
    val () = print! ("it has a carriage return (CRLF line endings)")
    val () = println! (_how_to_fix)
  in Kind_rejected() end
  else let
    val bad_structure = _structure_scan(cb, ck, ab, an, 0)
  in
    if bad_structure < ck then let
      val () = _rejected_head(b, s, e, pb, fs, fe)
      val () = _show_line(cb, ck, bad_structure)
      val () = print! (" is not a line the allowlist knows among those indented under six spaces (a key, a name, a whole line)")
      val () = println! (_how_to_fix)
    in Kind_rejected() end
    else let
      val bad_caller = _caller_scan(cb, ck, ab, an, 0)
    in
      if bad_caller >= ck then let
        val () = print! ("   ")
        val () = _print_range(pb, fs, fe)
        val () = println! (": pass, a caller of a shared workflow (every line is a line the allowlist knows)")
      in Kind_caller() end
      else let
        val state = _setup_scan(cb, ck, ab, an, _is_bats(b, s, e), 0, 0)
      in
        if state = 9 || state = 4 || state = 5 then let
          val () = print! ("   ")
          val () = _print_range(pb, fs, fe)
          val () = println! (": pass, runs jobs and calls the setup action in the canonical step")
        in Kind_runner() end
        else let
          val () = _rejected_head(b, s, e, pb, fs, fe)
          val () = print! ("as a caller of a shared workflow its ")
          val () = _show_line(cb, ck, bad_caller)
          val () = print! (" is not a line the allowlist knows, and as a file that runs jobs it has no line \"    steps:\" followed by the checkout step and then the canonical setup step (\"- name: Set up bats\", its uses: of bats-lang/bats/.github/actions/setup at a full commit, the next step)")
          val () = println! (_how_to_fix)
        in Kind_rejected() end
      end
    end
  end
end

(* Why a workflow file could not be read, as a rejected file's message *)
fn _unreadable {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; fs <= fe; fe <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe,
   status: int, read_end: drained): void = let
  val () = _error_line(b, s, e)
  val () = print! ("workflow ")
  val () = _print_range(pb, fs, fe)
in
  case+ read_end of
  | Drained_whole() => println! (" could not be read (cat status ", status, ")")
  | Drained_too_long() => println! (" does not fit the 524288-byte buffer, so the audit would see part of it")
  | Drained_failed() => println! (" could not be read to its end")
end

(* One workflow, pb[fs, fe), of the repository b[s, e): its kind *)
fn _audit_file {l,l2,la:agz}{s,e,fs,fe,an:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288; an <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   pb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe,
   ab: !$A.borrow(byte, la, 524288), an: int an): kind =
  if fe - fs <= 255 then let
    var content : $B.builder(0) = $B.create()
    val @(cat_status, cat_end) = _capture("cat", _cat_argv(b, s, e, pb, fs, fe), content)
    val @(content_arr, ck) = $B.to_arr(content)
    val @(cfz, cb) = $A.freeze<byte>(content_arr)
    var sum_out : $B.builder(0) = $B.create()
    val @(sum_status, sum_end) = _capture("sha256sum", _sum_argv(b, s, e, pb, fs, fe), sum_out)
    val @(sum_arr, hk) = $B.to_arr(sum_out)
    val @(hfz, hb) = $A.freeze<byte>(sum_arr)
    val readable =
      (case+ cat_end of
       | Drained_whole() => cat_status = 0
       | Drained_too_long() => false
       | Drained_failed() => false): bool
    val hashed =
      (case+ sum_end of
       | Drained_whole() => sum_status = 0
       | Drained_too_long() => false
       | Drained_failed() => false): bool
    val k =
      (if readable then _classify(b, s, e, pb, fs, fe, cb, ck, hb, hk, hashed, ab, an)
       else let
         val () = _unreadable(b, s, e, pb, fs, fe, cat_status, cat_end)
       in Kind_rejected() end): kind
    val () = $A.drop<byte>(hfz, hb)
    val () = $A.free<byte>($A.thaw<byte>(hfz))
    val () = $A.drop<byte>(cfz, cb)
    val () = $A.free<byte>($A.thaw<byte>(cfz))
  in k end
  else let
    val () = _error_line(b, s, e)
  in (println! ("a workflow path of ", fe - fs, " bytes is longer than the ", 255, " the audit will put in an argument"); Kind_rejected()) end

(* Every workflow in fb[i, k), one on each line, of the repository b[s, e):
   the counts go on from t *)
fun _audit_files {l,l2,la:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{k:nat | k <= 524288}{i:nat | i <= k}{an:nat | an <= 524288} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), k: int k, i: int i,
   ab: !$A.borrow(byte, la, 524288), an: int an, t: tally): tally = let
  val j = _line_end(fb, k, i)
  val t2 =
    (if j > i then _count(t, _audit_file(b, s, e, fb, i, j, ab, an))
     else t): tally
in
  if j >= k then t2 else _audit_files(b, s, e, fb, k, j + 1, ab, an, t2)
end

(* The workflows of the clone of b[s, e), from the run of the listing: the
   counts go on from t *)
fn _audit_workflows {l,la:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{an:nat | an <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   status: int, read_end: drained, files: $B.builder_v,
   ab: !$A.borrow(byte, la, 524288), an: int an, t: tally): tally = let
  val @(files_arr, files_len) = $B.to_arr(files)
  val @(fz, fb) = $A.freeze<byte>(files_arr)
  val @(files_n, listed_n, callers_n, runners_n, rejected_n) = t
  val t2 =
    (case+ read_end of
     | Drained_whole() =>
         if status = 0 then _audit_files(b, s, e, fb, files_len, 0, ab, an, t)
         else let
           val () = _error_line(b, s, e)
         in (println! ("git ls-files could not list the workflows (status ", status, ")"); @(files_n, listed_n, callers_n, runners_n, rejected_n + 1)) end
     | Drained_too_long() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows does not fit the 524288-byte buffer, so the audit would see part of it"); @(files_n, listed_n, callers_n, runners_n, rejected_n + 1)) end
     | Drained_failed() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows could not be read"); @(files_n, listed_n, callers_n, runners_n, rejected_n + 1)) end): tally
  val () = $A.drop<byte>(fz, fb)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in t2 end

(* Audits the clone of b[s, e): whether it failed, and the counts from t *)
fn _audit_clone {l,la:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{an:nat | an <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   ab: !$A.borrow(byte, la, 524288), an: int an, failing: !$B.sized_rope, t: tally): @(bool, tally) = let
  var files : $B.builder(0) = $B.create()
  val @(status, read_end) = _capture("git", _workflows_argv(b, s, e), files)
  val t2 = _audit_workflows(b, s, e, status, read_end, files, ab, an, t)
  val @(_, _, _, _, rejected_before) = t
  val @(_, _, _, _, rejected_after) = t2
  val pins = _run("env", _check_argv(b, s, e))
  val () =
    if pins = 0 then ()
    else let
      val () = _error_line(b, s, e)
    in println! ("bats check-pins --discover reports floating inputs, or could not run (status ", pins, "); its lines are above") end
  val failed = rejected_after != rejected_before || pins != 0: bool
  val () = if failed then _fail(b, s, e, failing) else ()
in @(failed, t2) end

(* Audits b[s, e): whether it failed, and the counts from t *)
fn _audit_one {l,la:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{an:nat | an <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   ab: !$A.borrow(byte, la, 524288), an: int an, failing: !$B.sized_rope, t: tally): @(bool, tally) = let
  val () = _header(b, s, e)
in
  if ~_name_ok(b, s, e, false) then let
    val () = _error_line(b, s, e)
    val () = println! ("the repository's name is not one the audit will put in a path")
    val () = _fail(b, s, e, failing)
  in @(true, t) end
  else let
    val cloned = _run("git", _clone_argv(b, s, e))
  in
    if cloned != 0 then let
      val () = _error_line(b, s, e)
      val () = println! ("cannot be cloned (git status ", cloned, ")")
      val () = _fail(b, s, e, failing)
    in @(true, t) end
    else _audit_clone(b, s, e, ab, an, failing, t)
  end
end

(* ============================================================
   The names, one on each line
   ============================================================ *)

(* Audits every name in b[i, k), one on each line: how many were audited and
   how many failed go on from audited and failed, and the counts of the
   workflows from t. A name over 255 bytes is a failure of its own, said and
   counted. *)
fun _audit_names {l,la:agz}{k:nat | k <= 524288}{i:nat | i <= k}{an:nat | an <= 524288} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i,
   ab: !$A.borrow(byte, la, 524288), an: int an,
   failing: !$B.sized_rope, audited: int, failed: int, t: tally): @(int, int, tally) = let
  val j = _line_end(b, k, i)
  val @(audited2, failed2, t2) =
    (if j <= i then @(audited, failed, t)
     else if j - i <= 255 then let
       val @(bad, t3) = _audit_one(b, i, j, ab, an, failing, t)
     in @(audited + 1, (if bad then failed + 1 else failed), t3) end
     else let
       val () = _header(b, i, j)
       val () = _error_line(b, i, j)
       val () = println! ("the repository's name is ", j - i, " bytes, longer than the ", 255, " the audit will put in a path")
       val () = _fail(b, i, j, failing)
     in @(audited + 1, failed + 1, t) end): @(int, int, tally)
in
  if j >= k then @(audited2, failed2, t2) else _audit_names(b, k, j + 1, ab, an, failing, audited2, failed2, t2)
end

(* The chunks of the failing names, in order, to stdout *)
fun _print_chunks {n:nat} .<n>. (chunks: $B.rope_sized_list(n)): void =
  case+ chunks of
  | ~$B.rope_sized_nil() => ()
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(fz, bv) = $A.freeze<byte>(chunk)
      val () = _print_range(bv, 0, used)
      val () = $A.drop<byte>(fz, bv)
      val () = $A.free<byte>($A.thaw<byte>(fz))
    in _print_chunks(rest) end

(* The organisation's non-archived repositories: gh's own jq keeps the names *)
fn _list_argv (): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("gh"),
  $L.list_vt_cons(_arg_s("api"),
  $L.list_vt_cons(_arg_s("--paginate"),
  $L.list_vt_cons(_arg_s("orgs/bats-lang/repos"),
  $L.list_vt_cons(_arg_s("--jq"),
  $L.list_vt_cons(_arg_s(".[] | select(.archived == false) | .name"),
    $L.list_vt_nil()))))))

(* The allowlist, from the file of this repository (the audit runs at the
   root of its checkout) *)
fn _allowlist_argv (): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("cat"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_s("tools/pin-audit/allowlist.txt"),
    $L.list_vt_nil())))

(* The audit of the names in names_bv, with the allowlist in allow_bv *)
fn _audit_all {l,la:agz}{k:nat | k <= 524288}{an:nat | an <= 524288}
  (names_bv: !$A.borrow(byte, l, 524288), k: int k,
   allow_bv: !$A.borrow(byte, la, 524288), an: int an): bool = let
  var failing : $B.sized_rope = $B.sized_rope_create()
  val @(audited, failed, files_n, listed_n, callers_n, runners_n, rejected_n) = let
    val @(audited0, failed0, counts) = _audit_names(names_bv, k, 0, allow_bv, an, failing, 0, 0, @(0, 0, 0, 0, 0))
    val @(a, b, c, d, f) = counts
  in @(audited0, failed0, a, b, c, d, f) end
  val () =
    if audited = 0 then
      println! ("::error title=pin audit::the list held no repository")
    else let
      val () = println! ("== ", files_n, " workflow files: ", listed_n, " listed by hash, ", callers_n,
                         " callers of a shared workflow, ", runners_n, " run jobs and call the setup action, ",
                         rejected_n, " not in the allowlist")
    in println! ("== ", audited, " repositories audited, ", failed, " failing") end
  val chunks = $B.sized_rope_chunks(failing)
  val () =
    if failed > 0 then let
      val () = print! ("== failing:")
      val () = _print_chunks(chunks)
    in println! () end
    else $B.rope_sized_list_free(chunks)
in audited > 0 && failed = 0 end

implement main0 () = let
  var allow : $B.builder(0) = $B.create()
  val @(allow_status, allow_end) = _capture("cat", _allowlist_argv(), allow)
  val allow_whole =
    (case+ allow_end of
     | Drained_whole() => allow_status = 0
     | Drained_too_long() => false
     | Drained_failed() => false): bool
  val @(allow_arr, allow_len) = $B.to_arr(allow)
  val @(allow_fz, allow_bv) = $A.freeze<byte>(allow_arr)
  var names : $B.builder(0) = $B.create()
  val @(status, read_end) = _capture("gh", _list_argv(), names)
  (* whether the list is whole and gh succeeded; every other outcome says
     which it was *)
  val listed =
    (case+ read_end of
     | Drained_whole() =>
         if status = 0 then true
         else let
           val () = println! ("::error title=pin audit::the organisation's repositories could not be listed (gh status ", status, ")")
         in false end
     | Drained_too_long() => let
         val () = println! ("::error title=pin audit::the list of the organisation's repositories does not fit the 524288-byte buffer, so the audit would see part of it")
       in false end
     | Drained_failed() => let
         val () = println! ("::error title=pin audit::the list of the organisation's repositories could not be read")
       in false end): bool
  val @(names_arr, names_len) = $B.to_arr(names)
  val @(names_fz, names_bv) = $A.freeze<byte>(names_arr)
  val ok =
    (if ~allow_whole then let
       val () = println! ("::error title=pin audit::the allowlist tools/pin-audit/allowlist.txt could not be read whole (cat status ", allow_status, ")")
     in false end
     else if ~listed then false
     else _audit_all(names_bv, names_len, allow_bv, allow_len)): bool
  val () = $A.drop<byte>(names_fz, names_bv)
  val () = $A.free<byte>($A.thaw<byte>(names_fz))
  val () = $A.drop<byte>(allow_fz, allow_bv)
  val () = $A.free<byte>($A.thaw<byte>(allow_fz))
in
  if ok then () else exit_void(1)
end
