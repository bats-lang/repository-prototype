(* support -- bytes, files, processes and hashes for pin-audit
   (bats-lang/repository-prototype#396). Keyword: pin-audit bounds.

   Every text is an array of 524288 bytes (a builder's to_arr) with its
   length, read through a borrow; a text that does not fit is the outcome
   Read_too_long, never a cut one. The audit reads no YAML: what is here
   is bytes, files and the tools the runner has (git, gh). *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use list as L
#use process as P
#use result as R
#use sha256 as H

(* How reading a file or a pipe ended: it all fit, it did not fit the
   524288-byte buffer, or a read failed. Every caller matches all three
   (case+). *)
#pub datatype read_end =
  | Read_whole
  | Read_too_long
  | Read_failed

(* ============================================================
   Ranges of bytes
   ============================================================ *)

fun _put_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{m:nat | m + (k - i) <= 524288} .<k - i>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int k,
   out: !$B.builder(m) >> $B.builder(m + (k - i))): void =
  if i >= k then ()
  else let
    val () = $B.put_char(out, $AR.low_byte(byte2int0($A.read<byte>(b, i))))
  in _put_range(b, i + 1, k, out) end

(* b[i, k) appended to out; the builder's length after is in its type *)
#pub fn put_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{m:nat | m + (k - i) <= 524288}
  (b: !$A.borrow(byte, l, n), i: int i, k: int k,
   out: !$B.builder(m) >> $B.builder(m + (k - i))): void

implement put_range (b, i, k, out) =
  _put_range(b, i, k, out)

fun _print_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n} .<k - i>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int k): void =
  if i >= k then ()
  else let
    val () = print_char(int2char0(byte2int0($A.read<byte>(b, i))))
  in _print_range(b, i + 1, k) end

(* b[i, k) to standard output *)
#pub fn print_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}
  (b: !$A.borrow(byte, l, n), i: int i, k: int k): void

implement print_range (b, i, k) =
  _print_range(b, i, k)

fun _line_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, stop: int): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if byte2int0($A.read<byte>(b, i)) = stop then i
  else _line_end(b, k, i + 1, stop)

(* The first place at or after i of b[0, k) where the byte is stop, or k *)
#pub fn find_byte {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, stop: int): [j:nat | i <= j; j <= k] int j

implement find_byte (b, k, i, stop) =
  _line_end(b, k, i, stop)

(* The end of the line that starts at i: the place of its newline, or k *)
#pub fn line_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i): [j:nat | i <= j; j <= k] int j

implement line_end (b, k, i) =
  _line_end(b, k, i, 10)

fun _range_eq {l,l2:agz}{n,n2:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n2} .<k - i>.
  (a: !$A.borrow(byte, l, n), i: int i, k: int k,
   b: !$A.borrow(byte, l2, n2), j: int j): bool =
  if i >= k then true
  else if byte2int0($A.read<byte>(a, i)) = byte2int0($A.read<byte>(b, j)) then _range_eq(a, i + 1, k, b, j + 1)
  else false

(* Whether a[i, k) is the same bytes as b[j, j + (k - i)) *)
#pub fn range_eq {l,l2:agz}{n,n2:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n2}
  (a: !$A.borrow(byte, l, n), i: int i, k: int k,
   b: !$A.borrow(byte, l2, n2), j: int j): bool

implement range_eq (a, i, k, b, j) =
  _range_eq(a, i, k, b, j)

fun _lit_from {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{sn:nat}{m:nat | m <= sn} .<sn - m>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, s: string sn, sn: int sn, m: int m): bool =
  if m >= sn then true
  else if i >= k then false
  else if byte2int0($A.read<byte>(b, i)) = char2int0(string_get_at(s, m)) then _lit_from(b, k, i + 1, s, sn, m + 1)
  else false

(* The place after the text s when b[0, k) has it at t, else ~1 *)
#pub fn lit_step {l:agz}{n:pos}{k:nat | k <= n}{t:nat | t <= k}{sn:pos}
  (b: !$A.borrow(byte, l, n), k: int k, t: int t, s: string sn)
  : [r:int | r < 0 || (r == t + sn && r <= k)] int r

implement lit_step (b, k, t, s) =
  if t + g1u2i(string1_length(s)) <= k then
    (if _lit_from(b, k, t, s, g1u2i(string1_length(s)), 0) then t + g1u2i(string1_length(s)) else ~1)
  else ~1

(* Whether the line b[ls, le) is exactly the text s *)
#pub fn line_is {l:agz}{n:pos}{le:nat | le <= n}{ls:nat | ls <= le}{sn:nat}
  (b: !$A.borrow(byte, l, n), ls: int ls, le: int le, s: string sn): bool

implement line_is (b, ls, le, s) =
  if le - ls = g1u2i(string1_length(s)) then _lit_from(b, le, ls, s, g1u2i(string1_length(s)), 0) else false

(* ============================================================
   Arguments
   ============================================================ *)

(* A text of the program as one argument *)
#pub fn arg_text {sn:nat | sn <= 524288} (s: string sn): $P.arg_entry

implement arg_text (s) = let
  var b : $B.builder(0) = $B.create()
  val () = $B.bput(b, s)
  val @(a, k) = $B.to_arr(b)
in @(a, k) end

(* leading text, then the bytes b[i, k), then trailing text, as one argument *)
#pub fn arg_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{pn,sn:nat | pn + (k - i) + sn <= 524288}
  (leading: string pn, b: !$A.borrow(byte, l, n), i: int i, k: int k, trailing: string sn): $P.arg_entry

implement arg_range (leading, b, i, k, trailing) = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, leading)
  val () = _put_range(b, i, k, out)
  val () = $B.bput(out, trailing)
  val @(a, kept) = $B.to_arr(out)
in @(a, kept) end

(* ============================================================
   Reading
   ============================================================ *)

(* Reads an open file or pipe to its end into out. A chunk that would take
   the builder past its capacity is not appended (nothing is cut): the
   outcome is Read_too_long. Each chunk is at least one byte, so the room
   left is the metric. *)
fun _drain {m:nat | m <= 524288} .<524288 - m>.
  (fd: !$F.fd, out: !$B.builder(m) >> $B.builder_v): read_end = let
  val chunk = $A.alloc<byte>(4096)
in
  case+ $F.file_read(fd, chunk, 4096) of
  | ~$R.err(_) => let val () = $A.free<byte>(chunk) in Read_failed() end
  | ~$R.ok(k) =>
    if k <= 0 then let val () = $A.free<byte>(chunk) in Read_whole() end
    else if $B.length(out) + k > 524288 then let val () = $A.free<byte>(chunk) in Read_too_long() end
    else let
      val @(fz, bv) = $A.freeze<byte>(chunk)
      val () = _put_range(bv, 0, k, out)
      val () = $A.drop<byte>(fz, bv)
      val () = $A.free<byte>($A.thaw<byte>(fz))
    in _drain(fd, out) end
end

fun _copy_path {l,l2:agz}{n:pos}{m:nat | m <= n}{c:pos | m < c}{i:nat | i <= m} .<m - i>.
  (p: !$A.borrow(byte, l, n), m: int m, dst: !$A.arr(byte, l2, c), i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(dst, i, $A.read<byte>(p, i))
  in _copy_path(p, m, dst, i + 1) end

(* The path p[0, m) opened for reading; the path is copied into an array of
   its own length and a zero, which file_open takes. *)
fn _open_read {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m): $R.result($F.fd, $F.io_error) = let
  val c = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, c, 0)
  val @(fz, bv) = $A.freeze<byte>(c)
  val r = $F.file_open(bv, m + 1, $F.ReadOnly(), $F.OpenExisting(), 0)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

(* The bytes of the file at the path p[0, m), read into out: how the read
   ended, and the words of the error when it failed (an empty text
   otherwise) *)
#pub fn read_file {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m, out: !$B.builder(0) >> $B.builder_v): @(read_end, string)

implement read_file (p, m, out) =
  case+ _open_read(p, m) of
  | ~$R.err(e) => @(Read_failed(), $F.io_error_text(e))
  | ~$R.ok(fd) => let
      val ended = _drain(fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in @(ended, "") end

(* ============================================================
   Processes
   ============================================================ *)

(* A program on PATH (or a path), with its arguments and the NAME=VALUE
   entries of extra added to the environment, the streams shared with this
   process: its exit status, or ~1 when it could not be run *)
#pub fn run_with {pn:nat | pn < 524288}
  (program: string pn, argv: $L.listv($P.arg_entry), extra: $L.listv($P.arg_entry)): int

implement run_with (program, argv, extra) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(fz, bv) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_with_proved(nul | bv, argv, extra, $P.inherit(), $P.inherit(), $P.inherit())
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

(* As run_with, the standard output read into out; the errors are shared.
   The read end is closed before the wait, so a child that wrote more than
   the buffer holds ends on a broken pipe and is not waited for forever. *)
#pub fn capture_with {pn:nat | pn < 524288}
  (program: string pn, argv: $L.listv($P.arg_entry), extra: $L.listv($P.arg_entry),
   out: !$B.builder(0) >> $B.builder_v): @(int, read_end)

implement capture_with (program, argv, extra, out) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(fz, bv) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_with_proved(nul | bv, argv, extra, $P.inherit(), $P.pipe_new(), $P.inherit())
  val () = $A.cborrow_drop(fz, bv)
  val () = $A.barr_free($A.barr_thaw(fz))
in
  case+ spawned of
  | ~$R.ok(sp) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = sp
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(serr_p)
      val+ ~$P.pipe_fd(out_fd) = sout_p
      val ended = _drain(out_fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(out_fd))
      val status = (case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in @(status, ended) end
  | ~$R.err(_) => @(~1, Read_whole())
end

(* ============================================================
   Hashes
   ============================================================ *)

(* The SHA-256 of content[0, k) as 64 lowercase hex digits *)
#pub fn sha256_hex {l:agz}{k:nat | k <= 524288}
  (content: !$A.arr(byte, l, 524288), k: int k): [lo:agz] $A.arr(byte, lo, 64)

implement sha256_hex (content, k) = let
  val ctx = $H.init()
  val () = $H.update(ctx, content, k)
  val out = $A.alloc<byte>(64)
  val () = $H.finish(ctx, out)
in out end


(* ============================================================
   Classes of bytes
   ============================================================ *)

(* Whether the byte c is in the class: 0 a decimal digit, 1 a character of
   a repository's name (letters, digits, '.', '_', '-'), 2 a character of a
   path (those and '/'), 3 printable ASCII (space to '~') *)
fn _in_class (c: int, cls: int): bool = let
  val digit = c >= 48 && c <= 57: bool
  val letter = (c >= 97 && c <= 122) || (c >= 65 && c <= 90): bool
  val mark = c = 46 || c = 95 || c = 45: bool
in
  if cls = 0 then digit
  else if cls = 1 then digit || letter || mark
  else if cls = 2 then digit || letter || mark || c = 47
  else c >= 32 && c <= 126
end

fun _class_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, cls: int): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if _in_class(byte2int0($A.read<byte>(b, i)), cls) then _class_end(b, k, i + 1, cls)
  else i

(* The end of the run of bytes of the class that starts at i of b[0, k) *)
#pub fn class_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, cls: int): [j:nat | i <= j; j <= k] int j

implement class_end (b, k, i, cls) = _class_end(b, k, i, cls)

(* How many digits (at most two) are at i of b[0, k) *)
#pub fn digits_upto_two {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i): [c:nat | c <= 2; i + c <= k] int c

implement digits_upto_two (b, k, i) =
  if i >= k then 0
  else if _in_class(byte2int0($A.read<byte>(b, i)), 0) then
    (if i + 1 >= k then 1
     else if _in_class(byte2int0($A.read<byte>(b, i + 1)), 0) then 2
     else 1)
  else 0

fun _hex_run {l:agz}{n:pos}{k:nat | k <= n}{i:nat}{c:nat} .<c>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, c: int c)
  : [r:int | r < 0 || (r == i + c && r <= k)] int r =
  if c <= 0 then (if i <= k then i else ~1)
  else if i >= k then ~1
  else let
    val x = byte2int0($A.read<byte>(b, i))
  in
    if (x >= 48 && x <= 57) || (x >= 97 && x <= 102) then
      (let val r = _hex_run(b, k, i + 1, c - 1) in if r >= 0 then r else ~1 end)
    else ~1
  end

(* The place after c lowercase hexadecimal digits at i of b[0, k), else ~1 *)
#pub fn hex_step {l:agz}{n:pos}{k:nat | k <= n}{i:nat}{c:nat}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, c: int c)
  : [r:int | r < 0 || (r == i + c && r <= k)] int r

implement hex_step (b, k, i, c) = _hex_run(b, k, i, c)


fun _range_eq_in {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n} .<k - i>.
  (a: !$A.borrow(byte, l, n), i: int i, k: int k, j: int j): bool =
  if i >= k then true
  else if byte2int0($A.read<byte>(a, i)) = byte2int0($A.read<byte>(a, j)) then _range_eq_in(a, i + 1, k, j + 1)
  else false

(* Whether a[i, k) is the same bytes as a[j, j + (k - i)), in one array *)
#pub fn range_eq_in {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n}
  (a: !$A.borrow(byte, l, n), i: int i, k: int k, j: int j): bool

implement range_eq_in (a, i, k, j) = _range_eq_in(a, i, k, j)


(* The entries of the directory at the path p[0, m) *)
#pub fn dir_entries {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m): $R.result([k:nat] $F.entries(k), $F.io_error)

implement dir_entries (p, m) = let
  val c = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, c, 0)
  val @(fz, bv) = $A.freeze<byte>(c)
  val r = $F.dir_read(bv, m + 1)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end


(* p[0, m) copied to dst[0, m) *)
#pub fn copy_into {l,l2:agz}{n:pos}{m:nat | m <= n}{c:pos | m < c}
  (p: !$A.borrow(byte, l, n), m: int m, dst: !$A.arr(byte, l2, c)): void

implement copy_into (p, m, dst) = _copy_path(p, m, dst, 0)


(* The file at a constant path, read into out *)
#pub fn read_constant {sn:nat | sn < 4096}
  (path: string sn, out: !$B.builder(0) >> $B.builder_v): @(read_end, string)

implement read_constant (path, out) = let
  var pb : $B.builder(0) = $B.create()
  val () = $B.bput(pb, path)
  val @(parr, pk) = $B.to_arr(pb)
  val @(fz, bv) = $A.freeze<byte>(parr)
  val r = read_file(bv, pk, out)
  val () = $A.drop<byte>(fz, bv)
  val () = $A.free<byte>($A.thaw<byte>(fz))
in r end

fun _copy_to {l,l2:agz}{n:pos}{m:nat | m <= n}{c:pos | m <= c}{i:nat | i <= m} .<m - i>.
  (p: !$A.borrow(byte, l, n), m: int m, dst: !$A.arr(byte, l2, c), i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(dst, i, $A.read<byte>(p, i))
  in _copy_to(p, m, dst, i + 1) end

(* The file at the path p[0, m) made (or emptied, or with append added to)
   to hold c[0, ck): whether it was written whole. For the tests'
   planted repositories. *)
#pub fn write_file {l,lc:agz}{n:pos}{m:nat | m <= n; m < 524288}{cn:pos | cn <= 524288}{ck:nat | ck <= cn}
  (p: !$A.borrow(byte, l, n), m: int m, c: !$A.borrow(byte, lc, cn), ck: int ck, append: bool): bool

implement write_file (p, m, c, ck, append) = let
  val pc = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, pc, 0)
  val @(pfz, pbv) = $A.freeze<byte>(pc)
  val opened = $F.file_open(pbv, m + 1, $F.WriteOnly(), (if append then $F.CreateOrAppend() else $F.CreateOrTruncate()), 420)
  val () = $A.drop<byte>(pfz, pbv)
  val () = $A.free<byte>($A.thaw<byte>(pfz))
in
  case+ opened of
  | ~$R.err(_) => false
  | ~$R.ok(fd) =>
    if ck <= 0 then let
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in true end
    else let
      val e = $A.alloc<byte>(ck)
      val () = _copy_to(c, ck, e, 0)
      val @(efz, ebv) = $A.freeze<byte>(e)
      val written = $F.file_write(fd, ebv, ck)
      val () = $A.drop<byte>(efz, ebv)
      val () = $A.free<byte>($A.thaw<byte>(efz))
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in
      case+ written of
      | ~$R.ok(_) => true
      | ~$R.err(_) => false
    end
end
