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
   3. Every workflow of the clone (.github/workflows/*.yml and *.yaml) that
      has steps calls bats's setup action. Has steps: a line, not a comment,
      with `steps:` in it (`git grep -l`); the workflow runs jobs itself,
      where a caller of a shared workflow (relock.yml, publish.yml) has none
      and is not asked. Nothing has to be recognised as running bats: a
      workflow with steps and no setup step fails, whatever its steps run,
      and the rule has no exception. The setup step: a key `uses:` of a step
      of the list under a job's `steps:`, of
      bats-lang/bats/.github/actions/setup at a full commit; in the
      repository bats alone, ./.github/actions/setup too (in any other
      repository that path is the repository's own action). The step is
      enabled only if neither it nor its job has a key `if:` at all (a
      condition is not evidence that the step runs; such a workflow fails
      with "conditional"). The text of a run block, a comment and a `uses:`
      of another indentation are not a step (`grep -Pz`, one run for each
      such file). The setup action is what runs the pin check, so a workflow
      with steps that does not call it skips it.
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


(* The regular expressions of the setup rule. They are read by tools (git
   grep -E, grep -P, grep -E); the program only names them. Keyword: setup
   rule (the research and the cases are on #365). *)

(* a blank line or a comment line *)
val _blank_line = "[ ]*(?:#[^\\n]*)?\\r?\\n"

(* the header of a block scalar (a line ending in | or >, with its
   indentation and chomping marks) *)
val _block_header = "[^\\n]*[:-][ ]+[|>][-+0-9]*[ ]*(?:#[^\\n]*)?\\r?\\n"

(* a key if:, any value (a quote around the key is allowed) *)
val _if_key = "[\"']?if[\"']?:"

(* a key uses: of bats's setup action at a full commit, to the end of its
   line (a quote and a comment after it are allowed); the local path
   ./.github/actions/setup is taken only in the repository bats, where it is
   bats's own action *)
val _uses_head = "uses:[ ]*[\"']?(?:"
val _uses_path_local = "\\./\\.github/actions/setup|"
val _uses_tail =
  "bats-lang/bats/\\.github/actions/setup@[0-9a-f]{40})[\"']?[ ]*(?:#[^\\n]*)?\\r?\\n"

(* from the first line of a step to the column of its key uses: (resp. if:)
   with the lines of the step between, the first such key and no earlier *)
val _skip_to_uses =
  "[^\\n]*+\\n(?:(?!\\g{d}[ ]\\g{p}uses:)(?:\\g{d}[ ]++[^\\n]*+\\n|[ ]*(?:#[^\\n]*)?\\r?\\n))*+\\g{d}[ ]\\g{p}"
val _skip_to_if =
  "[^\\n]*+\\n(?:(?!\\g{d}[ ]\\g{p}[\"']?if[\"']?:)(?:\\g{d}[ ]++[^\\n]*+\\n|[ ]*(?:#[^\\n]*)?\\r?\\n))*+\\g{d}[ ]\\g{p}"

(* The regular expression held by a rope, as an argument. A regular
   expression is a few kilobytes, so it is one chunk; a rope of more is not
   cut: the argument is the pattern `(`, which grep rejects with status 2,
   and the audit says so. *)
fn _rope_arg (r: $B.sized_rope): $P.arg_entry = let
  val chunks = $B.sized_rope_chunks(r)
in
  case+ chunks of
  | ~$B.rope_sized_nil() => _arg_s("")
  | ~$B.rope_sized_cons(chunk, used, rest) =>
    (case+ rest of
     | ~$B.rope_sized_nil() => @(chunk, used)
     | ~$B.rope_sized_cons(chunk2, _, rest2) => let
         val () = $A.free<byte>(chunk2)
         val () = $B.rope_sized_list_free(rest2)
         val () = $A.free<byte>(chunk)
       in _arg_s("(") end)
end

(* A line that is not a comment with `steps:` in it, not as the end of a
   longer word: a flow-style `steps: [...]` and a `steps:` after other keys
   on a line count, so a workflow that has steps is never taken for a caller
   of a shared workflow *)
val _steps_line = "^([^#]*[^#A-Za-z0-9_.-])?steps:"

(* The workflows of the clone that have steps: a file with a line that has
   `steps:` in it (a job of its own, so the file runs jobs itself). One path
   on each line; git grep's status is 0 for some, 1 for none. A workflow
   whose jobs only `uses:` a shared workflow (relock.yml, publish.yml) has
   none. *)
fn _workflows_argv {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("git"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("grep"),
  $L.list_vt_cons(_arg_s("-l"),
  $L.list_vt_cons(_arg_s("-E"),
  $L.list_vt_cons(_arg_s("-e"),
  $L.list_vt_cons(_arg_s(_steps_line),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yml"),
  $L.list_vt_cons(_arg_s(":(glob).github/workflows/*.yaml"),
    $L.list_vt_nil())))))))))))

(* A step of the file that calls bats's setup action. grep -P over the whole
   file (-z). The steps are the list under a `steps:` that is not inside a
   block scalar, at the indentation of its first dash, and a key of a step
   is at the column of the first key; the job is the mapping that holds the
   `steps:` key, whose keys are at its column. So the text of a run block, a
   comment and a `uses:` of another indentation are not a step. With
   enabled, the step must have no key `if:` and neither must its job (any
   value: a condition is not evidence that the step runs); without it, the
   same test with the `if:` keys ignored, which says a step is there and is
   conditional. in_bats says the local path counts too. *)
fn _setup_regex (in_bats: bool, enabled: bool): $P.arg_entry = let
  var out : $B.sized_rope = $B.sized_rope_create()
  val () = $B.sized_rope_bput(out, "(?m)")
  (* the start of the file to a job header (a line that ends in a colon), a
     block scalar (a header that ends in | or >, and the lines indented under
     it) taken whole and never entered *)
  val () = $B.sized_rope_bput(out, "\\A(?:(?>(?<h>[ ]*)")
  val () = $B.sized_rope_bput(out, _block_header)
  val () = $B.sized_rope_bput(out, "(?:\\g{h}[ ]+[^\\n]*+\\n|[ ]*\\r?\\n)*)|(?!")
  val () = $B.sized_rope_bput(out, _block_header)
  val () = $B.sized_rope_bput(out, ")[^\\n]*+\\n)*?")
  val () = $B.sized_rope_bput(out, "(?<j>[ ]*+)[^\\s#][^\\n]*:[ ]*(?:#[^\\n]*)?\\r?\\n")
  (* s: the column of the keys of the job, which is the column of its steps: *)
  val () = $B.sized_rope_bput(out, "(?:")
  val () = $B.sized_rope_bput(out, _blank_line)
  val () = $B.sized_rope_bput(out, ")*+(?=(?<s>\\g{j}[ ]++))")
  (* the keys of the job before steps:, none of them an if: when enabled *)
  val () = $B.sized_rope_bput(out, "(?:")
  val () = $B.sized_rope_bput(out, _blank_line)
  val () = $B.sized_rope_bput(out, "|\\g{s}(?!")
  val () = (if enabled then $B.sized_rope_bput(out, _if_key) else $B.sized_rope_bput(out, "(?!)"))
  val () = $B.sized_rope_bput(out, "|steps:)[^\\n]*+\\n)*+")
  val () = $B.sized_rope_bput(out, "\\g{s}steps:[ ]*(?:#[^\\n]*)?\\r?\\n")
  (* and none after it *)
  val () =
    if enabled then let
      val () = $B.sized_rope_bput(out, "(?!(?:")
      val () = $B.sized_rope_bput(out, _blank_line)
      val () = $B.sized_rope_bput(out, "|\\g{s}(?!")
      val () = $B.sized_rope_bput(out, _if_key)
      val () = $B.sized_rope_bput(out, ")[^\\n]*+\\n)*+\\g{s}")
      val () = $B.sized_rope_bput(out, _if_key)
      val () = $B.sized_rope_bput(out, ")")
    in () end
    else ()
  (* d: the indentation of the list's dashes *)
  val () = $B.sized_rope_bput(out, "(?=(?:")
  val () = $B.sized_rope_bput(out, _blank_line)
  val () = $B.sized_rope_bput(out, ")*(?<d>\\g{s}[ ]*)-)")
  (* the list, up to the step this test looks at; p: the spaces after its dash *)
  val () = $B.sized_rope_bput(out, "(?:\\g{d}-[^\\n]*+\\n|\\g{d}[ ]++[^\\n]*+\\n|")
  val () = $B.sized_rope_bput(out, _blank_line)
  val () = $B.sized_rope_bput(out, ")*?\\g{d}-(?<p>[ ]+)")
  (* it has the key uses: as the first key or later *)
  val () = $B.sized_rope_bput(out, "(?=")
  val () = $B.sized_rope_bput(out, _uses_head)
  val () = (if in_bats then $B.sized_rope_bput(out, _uses_path_local) else ())
  val () = $B.sized_rope_bput(out, _uses_tail)
  val () = $B.sized_rope_bput(out, "|")
  val () = $B.sized_rope_bput(out, _skip_to_uses)
  val () = $B.sized_rope_bput(out, _uses_head)
  val () = (if in_bats then $B.sized_rope_bput(out, _uses_path_local) else ())
  val () = $B.sized_rope_bput(out, _uses_tail)
  val () = $B.sized_rope_bput(out, ")")
  (* and, when enabled, no key if: in the step *)
  val () =
    if enabled then let
      val () = $B.sized_rope_bput(out, "(?!")
      val () = $B.sized_rope_bput(out, _if_key)
      val () = $B.sized_rope_bput(out, "|")
      val () = $B.sized_rope_bput(out, _skip_to_if)
      val () = $B.sized_rope_bput(out, _if_key)
      val () = $B.sized_rope_bput(out, ")")
    in () end
    else ()
in _rope_arg(out) end

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

(* Whether one workflow of the clone has a step that calls the setup action
   (enabled, or just conditional): grep's status, 0 for found, 1 for none,
   2 for an error *)
fn _setup_argv {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255;
                                           fs <= fe; fe <= 524288; fe - fs <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe, enabled: bool): $L.listv($P.arg_entry) =
  $L.list_vt_cons(_arg_s("env"),
  $L.list_vt_cons(_arg_s("-C"),
  $L.list_vt_cons(_arg_name("audit-clones/", b, s, e, ""),
  $L.list_vt_cons(_arg_s("grep"),
  $L.list_vt_cons(_arg_s("-P"),
  $L.list_vt_cons(_arg_s("-z"),
  $L.list_vt_cons(_arg_s("-q"),
  $L.list_vt_cons(_arg_s("-e"),
  $L.list_vt_cons(_setup_regex(_is_bats(b, s, e), enabled),
  $L.list_vt_cons(_arg_s("--"),
  $L.list_vt_cons(_arg_name("", fb, fs, fe, ""),
    $L.list_vt_nil())))))))))))

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


(* The counts of the workflows that have steps, over a repository or the whole
   run: how many there are, how many call bats's setup action and how many
   fail *)
typedef tally = @(int, int, int)

(* One workflow, fb[fs, fe), of the repository b[s, e): 0 when it has an
   enabled step that calls the setup action, else 1 and the error that says
   why *)
fn _audit_file {l,l2:agz}{s,e,fs,fe:nat | s <= e; e <= 524288; e - s <= 255; fs <= fe; fe <= 524288}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), fs: int fs, fe: int fe): int =
  if fe - fs <= 255 then let
    val setup = _run("env", _setup_argv(b, s, e, fb, fs, fe, true))
  in
    if setup = 0 then 0
    else if setup = 1 then let
      val conditional = _run("env", _setup_argv(b, s, e, fb, fs, fe, false))
      val () = _error_line(b, s, e)
      val () = print! ("workflow ")
      val () = _print_range(fb, fs, fe)
    in
      if conditional = 0 then
        (println! (" has steps, and its step that calls bats's setup action is conditional (an if: on the step or on its job), so the pin check may never run in it"); 1)
      else
        (println! (" has steps and no enabled step that calls bats's setup action (bats-lang/bats/.github/actions/setup at a full commit; ./.github/actions/setup in bats itself), so the pin check never runs in it"); 1)
    end
    else let
      val () = _error_line(b, s, e)
      val () = print! ("grep could not look for a step of the setup action in ")
      val () = _print_range(fb, fs, fe)
    in (println! (" (status ", setup, ")"); 1) end
  end
  else let
    val () = _error_line(b, s, e)
  in (println! ("a workflow path of ", fe - fs, " bytes is longer than the ", 255, " the audit will put in an argument"); 1) end

(* Every workflow in fb[i, k), one on each line, of the repository b[s, e):
   the counts go on from t *)
fun _audit_files {l,l2:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   fb: !$A.borrow(byte, l2, 524288), k: int k, i: int i, t: tally): tally = let
  val j = _line_end(fb, k, i)
  val t2 =
    (if j > i then let
       val code = _audit_file(b, s, e, fb, i, j)
       val @(with_steps, calling, failing) = t
     in
       (if code = 0 then @(with_steps + 1, calling + 1, failing)
        else @(with_steps + 1, calling, failing + 1))
     end
     else t): tally
in
  if j >= k then t2 else _audit_files(b, s, e, fb, k, j + 1, t2)
end

(* What the setup rule finds in the clone of b[s, e), from the run of the
   workflows listing: the counts go on from t *)
fn _without_setup {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e,
   status: int, read_end: drained, files: $B.builder_v, t: tally): tally = let
  val @(files_arr, files_len) = $B.to_arr(files)
  val @(fz, fb) = $A.freeze<byte>(files_arr)
  val @(with_steps, calling, failing) = t
  val t2 =
    (case+ read_end of
     | Drained_whole() =>
         if status = 0 then _audit_files(b, s, e, fb, files_len, 0, t)
         else if status = 1 then t
         else let
           val () = _error_line(b, s, e)
         in (println! ("git grep could not list the workflows that have steps (status ", status, ")"); @(with_steps, calling, failing + 1)) end
     | Drained_too_long() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows that have steps does not fit the 524288-byte buffer, so the audit would see part of it"); @(with_steps, calling, failing + 1)) end
     | Drained_failed() => let
         val () = _error_line(b, s, e)
       in (println! ("the list of workflows that have steps could not be read"); @(with_steps, calling, failing + 1)) end): tally
  val () = $A.drop<byte>(fz, fb)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in t2 end

(* Audits the clone of b[s, e): whether it failed, and the counts from t *)
fn _audit_clone {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e, failing: !$B.sized_rope, t: tally): @(bool, tally) = let
  var files : $B.builder(0) = $B.create()
  val @(status, read_end) = _capture("git", _workflows_argv(b, s, e), files)
  val t2 = _without_setup(b, s, e, status, read_end, files, t)
  val @(_, _, failing_before) = t
  val @(_, _, failing_after) = t2
  val pins = _run("env", _check_argv(b, s, e))
  val () =
    if pins = 0 then ()
    else let
      val () = _error_line(b, s, e)
    in println! ("bats check-pins --discover reports floating inputs, or could not run (status ", pins, "); its lines are above") end
  val failed = failing_after != failing_before || pins != 0: bool
  val () = if failed then _fail(b, s, e, failing) else ()
in @(failed, t2) end

(* Audits b[s, e): whether it failed, and the counts from t *)
fn _audit_one {l:agz}{s,e:nat | s <= e; e <= 524288; e - s <= 255}
  (b: !$A.borrow(byte, l, 524288), s: int s, e: int e, failing: !$B.sized_rope, t: tally): @(bool, tally) = let
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
    else _audit_clone(b, s, e, failing, t)
  end
end

(* ============================================================
   The names, one on each line
   ============================================================ *)

(* Audits every name in b[i, k), one on each line: how many were audited and
   how many failed go on from audited and failed, and the counts of the
   workflows from t. A name over 255 bytes is a failure of its own, said and
   counted. *)
fun _audit_names {l:agz}{k:nat | k <= 524288}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, 524288), k: int k, i: int i,
   failing: !$B.sized_rope, audited: int, failed: int, t: tally): @(int, int, tally) = let
  val j = _line_end(b, k, i)
  val @(audited2, failed2, t2) =
    (if j <= i then @(audited, failed, t)
     else if j - i <= 255 then let
       val @(bad, t3) = _audit_one(b, i, j, failing, t)
     in @(audited + 1, (if bad then failed + 1 else failed), t3) end
     else let
       val () = _header(b, i, j)
       val () = _error_line(b, i, j)
       val () = println! ("the repository's name is ", j - i, " bytes, longer than the ", 255, " the audit will put in a path")
       val () = _fail(b, i, j, failing)
     in @(audited + 1, failed + 1, t) end): @(int, int, tally)
in
  if j >= k then @(audited2, failed2, t2) else _audit_names(b, k, j + 1, failing, audited2, failed2, t2)
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
  val @(audited, failed, with_steps, calling, failing_workflows) =
    (if listed then let
       val @(audited0, failed0, counts) = _audit_names(names_bv, names_len, 0, failing, 0, 0, @(0, 0, 0))
       val @(a, b, c) = counts
     in @(audited0, failed0, a, b, c) end
     else @(0, 0, 0, 0, 0)): @(int, int, int, int, int)
  val () = $A.drop<byte>(names_fz, names_bv)
  val () = $A.free<byte>($A.thaw<byte>(names_fz))
  val () =
    if ~listed then ()
    else if audited = 0 then
      println! ("::error title=pin audit::the list held no repository")
    else let
      val () = println! ("== ", with_steps, " workflows with steps: ", calling, " call the setup action, ",
                         failing_workflows, " failing")
    in println! ("== ", audited, " repositories audited, ", failed, " failing") end
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
