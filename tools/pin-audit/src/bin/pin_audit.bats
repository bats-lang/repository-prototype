(* pin_audit -- the weekly audit of the organisation's CI pins
   (bats-lang/repository-prototype#365, piece 3 of #353; the audit #352 was).

   pin-audit

   1. The non-archived repositories of the organisation: `gh api --paginate
      orgs/bats-lang/repos`, its own jq keeping the names of those with
      archived false. Bats has no HTTP client (no package of the
      repository makes a request; bridge's fetch is the browser's), so the
      list is the GitHub CLI's, which the runner image ships and which
      reads the job's GH_TOKEN. A failed gh, or a list that does not fit,
      fails the run: an audit that saw part of the organisation says so.
   2. For each name, a shallow clone into audit-clones/<name> (git, one
      request for all of a repository's files, and the checker's own file
      discovery then reads them as it reads a checkout).
   3. Whether a workflow or action of the clone calls the bats setup action
      (git grep for a `uses:` of bats-lang/bats/.github/actions/setup at a
      full commit, or bats's own ./.github/actions/setup): the setup action
      is what runs the pin check, so a repository that never calls it skips
      the check.
   4. The checker itself: `bats check-pins --discover` inside the clone
      (env -C), its findings and the exceptions it lists
      (`# unpinned: <reason>`, listed and not failures) in the job log.

   Every failure is a `::error` line naming the repository; the run ends
   with the failing repositories and a status of 1, so the run is red and
   says which. Nothing in the clones is run: only read.

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

(* ============================================================
   Builders and arguments
   ============================================================ *)

fn _put (out: !$B.builder_v >> $B.builder_v, v: int): void =
  if $B.length(out) < 524288 then $B.put_char(out, $AR.low_byte(v)) else ()

fn _bput {sn:nat} (out: !$B.builder_v >> $B.builder_v, s: string sn): void = let
  fun loop {sl:nat}{i:nat | i <= sl} .<sl - i>.
    (out: !$B.builder_v >> $B.builder_v, s: string sl, n: int sl, i: int i): void =
    if i >= n then ()
    else let
      val () = _put(out, char2int0(string_get_at(s, i)))
    in loop(out, s, n, i + 1) end
in loop(out, s, g1u2i(string1_length(s)), 0) end

(* b[i, k) appended to out *)
fun _put_range {l:agz}{n:pos}{i:nat} .<max(n - i, 0)>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int, n: int n, out: !$B.builder_v >> $B.builder_v): void =
  if i >= k then ()
  else if i >= n then ()
  else let
    val () = _put(out, byte2int0($A.read<byte>(b, i)))
  in _put_range(b, i + 1, k, n, out) end

(* b[i, k) to stdout *)
fun _print_range {l:agz}{n:pos}{i:nat} .<max(n - i, 0)>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int, n: int n): void =
  if i >= k then ()
  else if i >= n then ()
  else let
    val () = print_char(int2char0(byte2int0($A.read<byte>(b, i))))
  in _print_range(b, i + 1, k, n) end

fn _arg (b: $B.builder_v): $P.arg_entry = let
  val @(a, k) = $B.to_arr(b)
in @(a, k) end

fn _arg_s {sn:nat} (s: string sn): $P.arg_entry = let
  var b : $B.builder_v = $B.create()
  val () = _bput(b, s)
in _arg(b) end

(* leading text, then the name b[s, e), then trailing text, as one argument *)
fn _arg_name {l:agz}{s,e:nat | s <= e} {pn,sn:nat}
  (leading: string pn, b: !$A.borrow(byte, l, 524288), s: int s, e: int e, trailing: string sn): $P.arg_entry = let
  var out : $B.builder_v = $B.create()
  val () = _bput(out, leading)
  val () = _put_range(b, s, e, 524288, out)
  val () = _bput(out, trailing)
in _arg(out) end

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

(* Reads a pipe to its end into out, at most fuel chunks of 4096 bytes:
   0 when it ended, 1 when it did not fit, 2 when a read failed *)
fun _drain {fuel:nat} .<fuel>.
  (fd: !$F.fd, out: !$B.builder_v >> $B.builder_v, fuel: int fuel): int =
  if fuel <= 0 then 1
  else let
    val chunk = $A.alloc<byte>(4096)
  in
    case+ $F.file_read(fd, chunk, 4096) of
    | ~$R.err(_) => let val () = $A.free<byte>(chunk) in 2 end
    | ~$R.ok(k) =>
      if k = 0 then let val () = $A.free<byte>(chunk) in 0 end
      else let
        val @(fz, bv) = $A.freeze<byte>(chunk)
        val () = _put_range(bv, 0, k, 4096, out)
        val () = $A.drop<byte>(fz, bv)
        val () = $A.free<byte>($A.thaw<byte>(fz))
      in _drain(fd, out, fuel - 1) end
  end

(* ============================================================
   1. The repositories
   ============================================================ *)

(* The names of the organisation's non-archived repositories, one on each
   line, appended to out: 0, or what went wrong (gh's own status, 100 + 1
   for a list too long for the buffer, 100 + 2 for a failed read, ~1 when gh
   could not be run) *)
fn _list_repositories (out: !$B.builder_v >> $B.builder_v): int = let
  val @(nul | path) = $P.path_of_string_proved("gh")
  val @(fz, bv) = $A.barr_freeze(path)
  val argv =
    $L.list_vt_cons(_arg_s("gh"),
    $L.list_vt_cons(_arg_s("api"),
    $L.list_vt_cons(_arg_s("--paginate"),
    $L.list_vt_cons(_arg_s("orgs/bats-lang/repos"),
    $L.list_vt_cons(_arg_s("--jq"),
    $L.list_vt_cons(_arg_s(".[] | select(.archived == false) | .name"),
      $L.list_vt_nil()))))))
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
      val drained = _drain(out_fd, out, 128)
      val () = $R.discard<int><$F.io_error>($F.file_close(out_fd))
      val status = (case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in if status != 0 then status else if drained != 0 then 100 + drained else 0 end
  | ~$R.err(_) => ~1
end

(* ============================================================
   2 to 4. One repository
   ============================================================ *)

(* Whether b[s, e) is a name GitHub gives a repository and the clone's path
   can hold: letters, digits, '.', '_' and '-', with a character that is
   not '.' (so never "." or ".."). The name goes into arguments, never a
   shell, and into audit-clones/<name>; nothing else may. *)
fun _name_ok {l:agz}{n:pos}{i:nat} .<max(n - i, 0)>.
  (b: !$A.borrow(byte, l, n), i: int i, e: int, n: int n, plain: bool): bool =
  if i >= e then plain
  else if i >= n then false
  else let
    val c = byte2int0($A.read<byte>(b, i))
    val letter = (c >= 97 && c <= 122) || (c >= 65 && c <= 90): bool
    val digit = c >= 48 && c <= 57: bool
    val dot = c = 46: bool
    val mark = c = 95 || c = 45: bool
  in
    if letter || digit || mark then _name_ok(b, i + 1, e, n, true)
    else if dot then _name_ok(b, i + 1, e, n, plain)
    else false
  end

(* The command line of the clone of b[s, e) *)
fn _clone_argv {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("clone"),
  $L.list_vt_cons(_arg_s("--quiet"),
  $L.list_vt_cons(_arg_s("--depth"),
  $L.list_vt_cons(_arg_s("1"),
  $L.list_vt_cons(_arg_name("https://github.com/bats-lang/", b, s, e, ".git"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
    $L.list_vt_nil())))))))

(* Whether a line of a workflow or action calls the setup action at a full
   commit (or bats's own, by path): git grep's status, 0 for found, 1 for
   none *)
fn _setup_argv {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("grep"),
  $L.list_vt_cons(_arg_s("-q"),
  $L.list_vt_cons(_arg_s("-E"),
  $L.list_vt_cons(_arg_s("^ *(- +)?uses: *([.]/[.]github/actions/setup|bats-lang/bats/[.]github/actions/setup@[0-9a-f]{40})"),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_s(".github"),
    $L.list_vt_nil())))))))))

(* The checker, run inside the clone *)
fn _check_argv {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("env"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("bats"),
  $L.list_vt_cons(_arg_s("check-pins"),
  $L.list_vt_cons(_arg_s("--discover"),
    $L.list_vt_nil()))))))

(* The repository's name: a header for its part of the log *)
fn _header {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): void = let
  val () = print! ("== ")
  val () = _print_range(b, s, e, 524288)
in println! () end

(* A failure, as the annotation that names the repository, and the name
   appended to the list of the failing *)
fn _fail {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   failing: !$B.builder_v >> $B.builder_v): void = let
  val () = _put(failing, 32)
in _put_range(b, s, e, 524288, failing) end

fn _error_line {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): void = let
  val () = print! ("::error title=pin audit::")
  val () = _print_range(b, s, e, 524288)
in print! (": ") end

(* Audits b[s, e): whether it failed *)
fn _audit_one {l:agz}{s,e:nat | s <= e}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   failing: !$B.builder_v >> $B.builder_v): bool = let
  val () = _header(b, s, e)
in
  if ~_name_ok(b, s, e, 524288, false) then let
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
    else let
      val setup = _run("git", _setup_argv(b, s, e))
      val pins = _run("env", _check_argv(b, s, e))
      val () =
        if setup = 0 then ()
        else if setup = 1 then let
          val () = _error_line(b, s, e)
        in println! ("no workflow or action calls bats's setup action (bats-lang/bats/.github/actions/setup at a full commit), so the pin check never runs here") end
        else let
          val () = _error_line(b, s, e)
        in println! ("git grep could not look for the setup action (status ", setup, ")") end
      val () =
        if pins = 0 then ()
        else let
          val () = _error_line(b, s, e)
        in println! ("bats check-pins --discover reports floating inputs, or could not run (status ", pins, "); its lines are above") end
      val failed = setup != 0 || pins != 0: bool
      val () = if failed then _fail(b, s, e, failing) else ()
    in failed end
  end
end

(* ============================================================
   The names, one on each line
   ============================================================ *)

(* Audits every name in b[i, k), the current one starting at start: how
   many were audited and how many failed go in counts *)
fun _audit_names {l:agz}{s,i:nat | s <= i} .<max(524288 - i, 0)>.
  (b: !$A.borrow(byte, l, 524288), start: int s, i: int i, k: int,
   failing: !$B.builder_v >> $B.builder_v, audited: int, failed: int): @(int, int) =
  if i >= k then
    (if i > start then let
       val bad = _audit_one(b, start, i, failing)
     in @(audited + 1, (if bad then failed + 1 else failed)) end
     else @(audited, failed))
  else if i >= 524288 then @(audited, failed)
  else if byte2int0($A.read<byte>(b, i)) = 10 then
    (if i > start then let
       val bad = _audit_one(b, start, i, failing)
     in _audit_names(b, i + 1, i + 1, k, failing, audited + 1, (if bad then failed + 1 else failed)) end
     else _audit_names(b, i + 1, i + 1, k, failing, audited, failed))
  else _audit_names(b, start, i + 1, k, failing, audited, failed)

implement main0 () = let
  var names : $B.builder_v = $B.create()
  val listed = _list_repositories(names)
  val @(a, k) = $B.to_arr(names)
  val @(fz, bv) = $A.freeze<byte>(a)
  var failing : $B.builder_v = $B.create()
  val @(audited, failed) =
    (if listed = 0 then _audit_names(bv, 0, 0, k, failing, 0, 0) else @(0, 0)): @(int, int)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
  val () =
    if listed != 0 then let
      val () = print! ("::error title=pin audit::the organisation's repositories could not be listed (status ")
      val () = print! (listed)
    in println! (")") end
    else if audited = 0 then
      println! ("::error title=pin audit::the list held no repository")
    else println! ("== ", audited, " repositories audited, ", failed, " failing")
  val @(fa, fk) = $B.to_arr(failing)
  val @(fz_f, bv_f) = $A.freeze<byte>(fa)
  val () =
    if failed > 0 then let
      val () = print! ("== failing:")
      val () = _print_range(bv_f, 0, fk, 524288)
    in println! () end
    else ()
  val () = $A.drop<byte>(fz_f, bv_f)
  val () = $A.free<byte>($A.thaw<byte>(fz_f))
in
  if listed != 0 || audited = 0 || failed > 0 then exit_void(1) else ()
end
