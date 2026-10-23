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
   3. Each workflow of the clone (.github/workflows/*.yml and *.yaml) that
      runs bats, that is, has a `steps:` and a bats command in the position
      of one (`bats check`, `bats build`, ...: `git grep -l --all-match`),
      must call bats's setup action in that same file (`uses:` of
      bats-lang/bats/.github/actions/setup at a full commit, or bats's own
      ./.github/actions/setup: `git grep -q`, one run for each such file).
      The setup action is what runs the pin check, so a workflow that sets
      bats up by hand skips it. A workflow with no steps of its own (a
      `uses:` of a shared workflow, as relock.yml and publish.yml are) or
      none that runs bats (review-gate*.yml, a Node or Gradle job) is not
      one that sets bats up and is not asked to call the action: the
      reason, with the research, is on #365. The rule is per file, not per
      job: a file whose other job calls the action passes.
   4. The checker itself: `bats check-pins --discover` inside the clone
      (env -C), its findings and the exceptions it lists
      (`# unpinned: <reason>`, listed and not failures) in the job log.

   Every failure is a `::error` line naming the repository (and, for step
   3, the workflow); the run ends with the failing repositories and a
   status of 1, so the run is red and says which. Nothing in the clones is
   run: only read.

   Bounds are in the types. A buffer is read at an index the types prove in
   range; an argument is built from a builder whose length the types prove
   fits; a text that does not fit its buffer (the list of repositories, the
   list of workflows) is the outcome `Drained_too_long`, which every caller
   matches with case+ and answers with an error and a failed run; the names
   of the failing repositories are a rope, which has no bound. Nothing is
   dropped and nothing ends early without saying so.

   The program is bats because we write bats (quire#646); the tools it calls
   (gh, git, env -C of GNU coreutils, bats) are the runner's and the
   pinned compiler's. *)

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

(* The workflows of the clone that run bats: a file with a `steps:` and a
   bats command in the position of one (the start of a line or after `- `,
   `run:`, `&&`, `||`, `|`, `;`, `(` or sudo, as bats's check-pins reads
   commands), one path on each line. git grep's status is 0 for some, 1 for
   none. A workflow whose jobs only `uses:` a shared workflow has no
   `steps:`, and its inputs that hold bats commands (relock.yml's
   `regenerate:`) are run by that workflow's own setup. *)
fn _workflows_argv {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("grep"),
  $L.list_vt_cons(_arg_s("-l"),
  $L.list_vt_cons(_arg_s("--all-match"),
  $L.list_vt_cons(_arg_s("-E"),
  $L.list_vt_cons(_arg_s("-e"),
  $L.list_vt_cons(_arg_s("^ +steps:"),
  $L.list_vt_cons(_arg_s("-e"),
  $L.list_vt_cons(_arg_s("(^ *(- +)?|run: *[|>]?-? *|(&&|[|;(]) *|sudo +)([.]/)?(dist/[a-z]+/)?bats +[a-z]"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yml"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yaml"),
    $L.list_vt_nil()))))))))))))))

(* Whether one workflow of the clone calls the setup action at a full commit
   (or bats's own, by path): git grep's status, 0 for found, 1 for none *)
fn _setup_argv {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255;
                                           fs <= fe; fe <= 524288; fe - fs <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("grep"),
  $L.list_vt_cons(_arg_s("-q"),
  $L.list_vt_cons(_arg_s("-E"),
  $L.list_vt_cons(_arg_s("^ *(- +)?uses: *([.]/[.]github/actions/setup|bats-lang/bats/[.]github/actions/setup@[0-9a-f]{40})"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_name(":(literal)", fb, fs, fe, ""),
    $L.list_vt_nil())))))))))

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

(* One workflow, fb[fs, fe), of the repository b[s, e): 0 when it calls the
   setup action, else 1 and the error that says so *)
fn _audit_file {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): int =
  if fe - fs <= 255 then let
    val setup = _run("git", _setup_argv(b, s, e, fb, fs, fe))
  in
    if setup = 0 then 0
    else if setup = 1 then let
      val () = _error_line(b, s, e)
      val () = print! ("workflow ")
      val () = _print_range(fb, fs, fe)
    in (println! (" runs bats but does not call bats's setup action (bats-lang/bats/.github/actions/setup at a full commit), so the pin check never runs in it"); 1) end
    else let
      val () = _error_line(b, s, e)
      val () = print! ("git grep could not look for the setup action in ")
      val () = _print_range(fb, fs, fe)
    in (println! (" (status ", setup, ")"); 1) end
  end
  else let
    val () = _error_line(b, s, e)
  in (println! ("a workflow path of ", fe - fs, " bytes is longer than the ", 255, " the audit will put in an argument"); 1) end

(* Every workflow in fb[i, k), one on each line, of the repository b[s, e):
   how many did not call the setup action, added to missing *)
fun _audit_files {l,l2:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), k: int k, i: int i, missing: int): int = let
  val j = _line_end(fb, k, i)
  val missing2 = (if j > i then missing + _audit_file(b, s, e, fb, i, j) else missing): int
in
  if j >= k then missing2 else _audit_files(b, s, e, fb, k, j + 1, missing2)
end

(* What the setup rule finds in the clone of b[s, e), from the run of the
   workflows listing: the number of failures (0 for none) *)
fn _without_setup {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   status: int, read_end: drained, files: $B.builder_v): int = let
  val @(files_arr, files_len) = $B.to_arr(files)
  val @(fz, fb) = $A.freeze<byte>(files_arr)
  val missing =
    (case+ read_end of
     | Drained_whole() =>
         if status = 0 then _audit_files(b, s, e, fb, files_len, 0, 0)
         else if status = 1 then 0
         else let
           val () = _error_line(b, s, e)
         in (println! ("git grep could not list the workflows that run bats (status ", status, ")"); 1) end
     | Drained_too_long() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows that run bats does not fit the 524288-byte buffer, so the audit would see part of it"); 1) end
     | Drained_failed() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows that run bats could not be read"); 1) end): int
  val () = $A.drop<byte>(fz, fb)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in missing end

(* Audits the clone of b[s, e): whether it failed *)
fn _audit_clone {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e, failing: !$B.sized_rope): bool = let
  var files : $B.builder(0) = $B.create()
  val @(status, read_end) = _capture("git", _workflows_argv(b, s, e), files)
  val missing = _without_setup(b, s, e, status, read_end, files)
  val pins = _run("env", _check_argv(b, s, e))
  val () =
    if pins = 0 then ()
    else let
      val () = _error_line(b, s, e)
    in println! ("bats check-pins --discover reports floating inputs, or could not run (status ", pins, "); its lines are above") end
  val failed = missing != 0 || pins != 0: bool
  val () = if failed then _fail(b, s, e, failing) else ()
in failed end

(* Audits b[s, e): whether it failed *)
fn _audit_one {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e, failing: !$B.sized_rope): bool = let
  val () = _header(b, s, e)
in
  if ~_name_ok(b, s, e, false) then let
    val () = _error_line(b, s, e)
    val () = println! ("the repository's name is not one the audit will put in a path")
    val () = _fail(b, s, e, failing)
  in true end
  else let
    val cloned = _run("git", _clone_argv(b, s, e))
  in
    if cloned != 0 then let
      val () = _error_line(b, s, e)
      val () = println! ("cannot be cloned (git status ", cloned, ")")
      val () = _fail(b, s, e, failing)
    in true end
    else _audit_clone(b, s, e, failing)
  end
end

(* ============================================================
   The names, one on each line
   ============================================================ *)

(* Audits every name in b[i, k), one on each line: how many were audited and
   how many failed go on from audited and failed. A name over 255 bytes
   is a failure of its own, said and counted. *)
fun _audit_names {l:agz}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i,
   failing: !$B.sized_rope, audited: int, failed: int): @(int, int) = let
  val j = _line_end(b, k, i)
  val @(audited2, failed2) =
    (if j <= i then @(audited, failed)
     else if j - i <= 255 then let
       val bad = _audit_one(b, i, j, failing)
     in @(audited + 1, (if bad then failed + 1 else failed)) end
     else let
       val () = _header(b, i, j)
       val () = _error_line(b, i, j)
       val () = println! ("the repository's name is ", j - i, " bytes, longer than the ", 255, " the audit will put in a path")
       val () = _fail(b, i, j, failing)
     in @(audited + 1, failed + 1) end): @(int, int)
in
  if j >= k then @(audited2, failed2) else _audit_names(b, k, j + 1, failing, audited2, failed2)
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

implement main0 () = let
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
  var failing : $B.sized_rope = $B.sized_rope_create()
  val @(audited, failed) =
    (if listed then _audit_names(names_bv, names_len, 0, failing, 0, 0) else @(0, 0)): @(int, int)
  val () = $A.drop<byte>(names_fz, names_bv)
  val () = $A.free<byte>($A.thaw<byte>(names_fz))
  val () =
    if ~listed then ()
    else if audited = 0 then
      println! ("::error title=pin audit::the list held no repository")
    else println! ("== ", audited, " repositories audited, ", failed, " failing")
  val chunks = $B.sized_rope_chunks(failing)
  val () =
    if failed > 0 then let
      val () = print! ("== failing:")
      val () = _print_chunks(chunks)
    in println! () end
    else $B.rope_sized_list_free(chunks)
in
  if ~listed || audited = 0 || failed > 0 then exit_void(1) else ()
end
