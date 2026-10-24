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
#use env as E
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

fun _range_eq {l,other_loc:agz}{n,other_size:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= other_size} .<k - i>.
  (left: !$A.borrow(byte, l, n), i: int i, k: int k,
   right: !$A.borrow(byte, other_loc, other_size), j: int j): bool =
  if i >= k then true
  else if byte2int0($A.read<byte>(left, i)) = byte2int0($A.read<byte>(right, j)) then _range_eq(left, i + 1, k, right, j + 1)
  else false

(* Whether left[i, k) is the same bytes as right[j, j + (k - i)) *)
#pub fn range_eq {l,other_loc:agz}{n,other_size:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= other_size}
  (left: !$A.borrow(byte, l, n), i: int i, k: int k,
   right: !$A.borrow(byte, other_loc, other_size), j: int j): bool

implement range_eq (left, i, k, right, j) =
  _range_eq(left, i, k, right, j)

fun _lit_from {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{literal_len:nat}{m:nat | m <= literal_len} .<literal_len - m>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, literal: string literal_len, literal_len: int literal_len, m: int m): bool =
  if m >= literal_len then true
  else if i >= k then false
  else if byte2int0($A.read<byte>(b, i)) = char2int0(string_get_at(literal, m)) then _lit_from(b, k, i + 1, literal, literal_len, m + 1)
  else false

(* The place after the text literal when b[0, k) has it at start, else ~1 *)
#pub fn lit_step {l:agz}{n:pos}{k:nat | k <= n}{start:nat | start <= k}{literal_len:pos}
  (b: !$A.borrow(byte, l, n), k: int k, start: int start, literal: string literal_len)
  : [after:int | after < 0 || (after == start + literal_len && after <= k)] int after

implement lit_step (b, k, start, literal) =
  if start + g1u2i(string1_length(literal)) <= k then
    (if _lit_from(b, k, start, literal, g1u2i(string1_length(literal)), 0) then start + g1u2i(string1_length(literal)) else ~1)
  else ~1

(* Whether the line b[line_start, line_stop) is exactly the text literal *)
#pub fn line_is {l:agz}{n:pos}{line_stop:nat | line_stop <= n}{line_start:nat | line_start <= line_stop}{literal_len:nat}
  (b: !$A.borrow(byte, l, n), line_start: int line_start, line_stop: int line_stop, literal: string literal_len): bool

implement line_is (b, line_start, line_stop, literal) =
  if line_stop - line_start = g1u2i(string1_length(literal)) then _lit_from(b, line_stop, line_start, literal, g1u2i(string1_length(literal)), 0) else false

(* ============================================================
   Arguments
   ============================================================ *)

(* A text of the program as one argument *)
#pub fn arg_text {text_len:nat | text_len <= 524288} (text: string text_len): $P.arg_entry

implement arg_text (text) = let
  var b : $B.builder(0) = $B.create()
  val () = $B.bput(b, text)
  val @(a, k) = $B.to_arr(b)
in @(a, k) end

(* leading text, then the bytes b[i, k), then trailing text, as one argument *)
#pub fn arg_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{leading_len,trailing_len:nat | leading_len + (k - i) + trailing_len <= 524288}
  (leading: string leading_len, b: !$A.borrow(byte, l, n), i: int i, k: int k, trailing: string trailing_len): $P.arg_entry

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
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val () = _put_range(view, 0, k, out)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
    in _drain(fd, out) end
end

fun _copy_path {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m < capacity}{i:nat | i <= m} .<m - i>.
  (p: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity), i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(p, i))
  in _copy_path(p, m, destination, i + 1) end

(* The path p[0, m) opened for reading; the path is copied into an array of
   its own length and a zero, which file_open takes. *)
fn _open_read {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m): $R.result($F.fd, $F.io_error) = let
  val path_copy = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, path_copy, 0)
  val @(frozen, view) = $A.freeze<byte>(path_copy)
  val opened = $F.file_open(view, m + 1, $F.ReadOnly(), $F.OpenExisting(), 0)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in opened end

(* The bytes of the file at the path p[0, m), read into out: how the read
   ended, and the words of the error when it failed (an empty text
   otherwise) *)
#pub fn read_file {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m, out: !$B.builder(0) >> $B.builder_v): @(read_end, string)

implement read_file (p, m, out) =
  case+ _open_read(p, m) of
  | ~$R.err(failure) => @(Read_failed(), $F.io_error_text(failure))
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
#pub fn run_with {program_len:nat | program_len < 524288}
  (program: string program_len, argv: $L.listv($P.arg_entry), extra: $L.listv($P.arg_entry)): int

implement run_with (program, argv, extra) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(frozen, view) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_with_proved(nul | view, argv, extra, $P.inherit(), $P.inherit(), $P.inherit())
  val () = $A.cborrow_drop(frozen, view)
  val () = $A.barr_free($A.barr_thaw(frozen))
in
  case+ spawned of
  | ~$R.ok(spawned_process) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = spawned_process
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val () = $P.pipe_end_close(serr_p)
    in case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1 end
  | ~$R.err(_) => ~1
end

(* As run_with, the standard output read into out; the errors are shared.
   The read end is closed before the wait, so a child that wrote more than
   the buffer holds ends on a broken pipe and is not waited for forever. *)
#pub fn capture_with {program_len:nat | program_len < 524288}
  (program: string program_len, argv: $L.listv($P.arg_entry), extra: $L.listv($P.arg_entry),
   out: !$B.builder(0) >> $B.builder_v): @(int, read_end)

implement capture_with (program, argv, extra, out) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(frozen, view) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_with_proved(nul | view, argv, extra, $P.inherit(), $P.pipe_new(), $P.inherit())
  val () = $A.cborrow_drop(frozen, view)
  val () = $A.barr_free($A.barr_thaw(frozen))
in
  case+ spawned of
  | ~$R.ok(spawned_process) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = spawned_process
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(serr_p)
      val+ ~$P.pipe_fd(out_fd) = sout_p
      val ended = _drain(out_fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(out_fd))
      val status = (case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in @(status, ended) end
  | ~$R.err(_) => @(~1, Read_whole())
end

(* As capture_with, but the standard error is read into out and the standard output is shared
   (the pin checker, bats-lang/repository-prototype#405: its failures are on its standard error) *)
#pub fn capture_error_with {program_len:nat | program_len < 524288}
  (program: string program_len, argv: $L.listv($P.arg_entry), extra: $L.listv($P.arg_entry),
   out: !$B.builder(0) >> $B.builder_v): @(int, read_end)

implement capture_error_with (program, argv, extra, out) = let
  val @(nul | path) = $P.path_of_string_proved(program)
  val @(frozen, view) = $A.barr_freeze(path)
  val spawned = $P.spawn_inherit_env_with_proved(nul | view, argv, extra, $P.inherit(), $P.inherit(), $P.pipe_new())
  val () = $A.cborrow_drop(frozen, view)
  val () = $A.barr_free($A.barr_thaw(frozen))
in
  case+ spawned of
  | ~$R.ok(spawned_process) => let
      val+ ~$P.spawn_pipes_mk(child, sin_p, sout_p, serr_p) = spawned_process
      val () = $P.pipe_end_close(sin_p)
      val () = $P.pipe_end_close(sout_p)
      val+ ~$P.pipe_fd(err_fd) = serr_p
      val ended = _drain(err_fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(err_fd))
      val status = (case+ $P.child_wait(child) of | ~$R.ok(n) => n | ~$R.err(_) => ~1): int
    in @(status, ended) end
  | ~$R.err(_) => @(~1, Read_whole())
end

(* ============================================================
   Hashes
   ============================================================ *)

(* The SHA-256 of content[0, k) as 64 lowercase hex digits *)
#pub fn sha256_hex {l:agz}{k:nat | k <= 524288}
  (content: !$A.arr(byte, l, 524288), k: int k): [out_loc:agz] $A.arr(byte, out_loc, 64)

implement sha256_hex (content, k) = let
  val context = $H.init()
  val () = $H.update(context, content, k)
  val out = $A.alloc<byte>(64)
  val () = $H.finish(context, out)
in out end


(* ============================================================
   Classes of bytes
   ============================================================ *)

(* The class of a run of bytes: a decimal digit, a character of a
   repository's name (letters, digits, '.', '_', '-'), a character of a path
   (those and '/'), printable ASCII (space to '~'). Every caller matches all
   four (case+). *)
#pub datatype byte_class =
  | Class_digit
  | Class_name
  | Class_path
  | Class_printable

(* Whether the byte byte_value is in the class *)
fn _in_class (byte_value: int, kind: byte_class): bool = let
  val digit = byte_value >= 48 && byte_value <= 57: bool
  val letter = (byte_value >= 97 && byte_value <= 122) || (byte_value >= 65 && byte_value <= 90): bool
  val mark = byte_value = 46 || byte_value = 95 || byte_value = 45: bool
in
  case+ kind of
  | Class_digit() => digit
  | Class_name() => digit || letter || mark
  | Class_path() => digit || letter || mark || byte_value = 47
  | Class_printable() => byte_value >= 32 && byte_value <= 126
end

fun _class_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, kind: byte_class): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if _in_class(byte2int0($A.read<byte>(b, i)), kind) then _class_end(b, k, i + 1, kind)
  else i

(* The end of the run of bytes of the class that starts at i of b[0, k) *)
#pub fn class_end {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, kind: byte_class): [j:nat | i <= j; j <= k] int j

implement class_end (b, k, i, kind) = _class_end(b, k, i, kind)

(* How many digits (at most two) are at i of b[0, k) *)
#pub fn digits_upto_two {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i): [c:nat | c <= 2; i + c <= k] int c

implement digits_upto_two (b, k, i) =
  if i >= k then 0
  else if _in_class(byte2int0($A.read<byte>(b, i)), Class_digit()) then
    (if i + 1 >= k then 1
     else if _in_class(byte2int0($A.read<byte>(b, i + 1)), Class_digit()) then 2
     else 1)
  else 0

fun _hex_run {l:agz}{n:pos}{k:nat | k <= n}{i:nat}{count:nat} .<count>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, count: int count)
  : [rest_end:int | rest_end < 0 || (rest_end == i + count && rest_end <= k)] int rest_end =
  if count <= 0 then (if i <= k then i else ~1)
  else if i >= k then ~1
  else let
    val digit = byte2int0($A.read<byte>(b, i))
  in
    if (digit >= 48 && digit <= 57) || (digit >= 97 && digit <= 102) then
      (let val rest_end = _hex_run(b, k, i + 1, count - 1) in if rest_end >= 0 then rest_end else ~1 end)
    else ~1
  end

(* The place after count lowercase hexadecimal digits at i of b[0, k), else ~1 *)
#pub fn hex_step {l:agz}{n:pos}{k:nat | k <= n}{i:nat}{count:nat}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, count: int count)
  : [after:int | after < 0 || (after == i + count && after <= k)] int after

implement hex_step (b, k, i, count) = _hex_run(b, k, i, count)


fun _range_eq_in {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n} .<k - i>.
  (text: !$A.borrow(byte, l, n), i: int i, k: int k, j: int j): bool =
  if i >= k then true
  else if byte2int0($A.read<byte>(text, i)) = byte2int0($A.read<byte>(text, j)) then _range_eq_in(text, i + 1, k, j + 1)
  else false

(* Whether text[i, k) is the same bytes as text[j, j + (k - i)), in one array *)
#pub fn range_eq_in {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}{j:nat | j + (k - i) <= n}
  (text: !$A.borrow(byte, l, n), i: int i, k: int k, j: int j): bool

implement range_eq_in (text, i, k, j) = _range_eq_in(text, i, k, j)


(* The entries of the directory at the path p[0, m) *)
#pub fn dir_entries {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m): $R.result([k:nat] $F.entries(k), $F.io_error)

implement dir_entries (p, m) = let
  val path_copy = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, path_copy, 0)
  val @(frozen, view) = $A.freeze<byte>(path_copy)
  val listed = $F.dir_read(view, m + 1)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in listed end


(* p[0, m) copied to destination[0, m) *)
#pub fn copy_into {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m < capacity}
  (p: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity)): void

implement copy_into (p, m, destination) = _copy_path(p, m, destination, 0)


(* The file at a constant path, read into out *)
#pub fn read_constant {constant_len:nat | constant_len < 4096}
  (path: string constant_len, out: !$B.builder(0) >> $B.builder_v): @(read_end, string)

implement read_constant (path, out) = let
  var path_builder : $B.builder(0) = $B.create()
  val () = $B.bput(path_builder, path)
  val @(path_array, path_len) = $B.to_arr(path_builder)
  val @(frozen, view) = $A.freeze<byte>(path_array)
  val read = read_file(view, path_len, out)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in read end

fun _copy_to {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m <= capacity}{i:nat | i <= m} .<m - i>.
  (p: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity), i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(p, i))
  in _copy_to(p, m, destination, i + 1) end

(* The file at the path p[0, m) made (or emptied, or with append added to)
   to hold content_text[0, content_len): whether it was written whole. For the tests'
   planted repositories. *)
#pub fn write_file {l,content_loc:agz}{n:pos}{m:nat | m <= n; m < 524288}{content_cap:pos | content_cap <= 524288}{content_len:nat | content_len <= content_cap}
  (p: !$A.borrow(byte, l, n), m: int m, content_text: !$A.borrow(byte, content_loc, content_cap), content_len: int content_len, append: bool): bool

implement write_file (p, m, content_text, content_len, append) = let
  val path_copy = $A.alloc<byte>(m + 1)
  val () = _copy_path(p, m, path_copy, 0)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_copy)
  val opened = $F.file_open(path_view, m + 1, $F.WriteOnly(), (if append then $F.CreateOrAppend() else $F.CreateOrTruncate()), 420)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in
  case+ opened of
  | ~$R.err(_) => false
  | ~$R.ok(fd) =>
    if content_len <= 0 then let
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in true end
    else let
      val copy_array = $A.alloc<byte>(content_len)
      val () = _copy_to(content_text, content_len, copy_array, 0)
      val @(bytes_frozen, bytes_view) = $A.freeze<byte>(copy_array)
      val written = $F.file_write(fd, bytes_view, content_len)
      val () = $A.drop<byte>(bytes_frozen, bytes_view)
      val () = $A.free<byte>($A.thaw<byte>(bytes_frozen))
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in
      case+ written of
      | ~$R.ok(_) => true
      | ~$R.err(_) => false
    end
end

(* Whether a file can be opened for reading at the path p[0, m) *)
#pub fn file_exists {l:agz}{n:pos}{m:nat | m <= n; m < 524288}
  (p: !$A.borrow(byte, l, n), m: int m): bool

implement file_exists (p, m) = let
  var probe : $B.builder(0) = $B.create()
  val @(ended, _) = read_file(p, m, probe)
  val () = $B.builder_free(probe)
in
  case+ ended of
  | Read_whole() => true
  | Read_too_long() => true
  | Read_failed() => false
end

(* Whether a file can be opened for reading at the constant path *)
#pub fn constant_exists {constant_len:nat | constant_len < 4096} (path: string constant_len): bool

implement constant_exists (path) = let
  var probe : $B.builder(0) = $B.create()
  val @(ended, _) = read_constant(path, probe)
  val () = $B.builder_free(probe)
in
  case+ ended of
  | Read_whole() => true
  | Read_too_long() => true
  | Read_failed() => false
end


(* ============================================================
   Helpers of the tests (the pin audit's and verify-archives')
   ============================================================ *)

(* The length of a text *)
#pub fn text_length {text_len:nat} (text: string text_len): int text_len

implement text_length (text) = g1u2i(string1_length(text))

#pub fn no_arguments (): $L.listv($P.arg_entry)

implement no_arguments () = $L.list_vt_nil()

#pub fn args1 (only: $P.arg_entry): $L.listv($P.arg_entry)

implement args1 (only) = $L.list_vt_cons(only, $L.list_vt_nil())

#pub fn args2 (first: $P.arg_entry, second: $P.arg_entry): $L.listv($P.arg_entry)

implement args2 (first, second) = $L.list_vt_cons(first, args1(second))

#pub fn args3 (first: $P.arg_entry, second: $P.arg_entry, third: $P.arg_entry): $L.listv($P.arg_entry)

implement args3 (first, second, third) = $L.list_vt_cons(first, args2(second, third))

#pub fn args4 (first: $P.arg_entry, second: $P.arg_entry, third: $P.arg_entry, fourth: $P.arg_entry): $L.listv($P.arg_entry)

implement args4 (first, second, third, fourth) = $L.list_vt_cons(first, args3(second, third, fourth))

(* program with the arguments, whose first is the program's own name: its
   status, ~1 when it could not be run *)
#pub fn run_program {program_len:nat | program_len < 4096}
  (prog: string program_len, args: $L.listv($P.arg_entry)): int

implement run_program (prog, args) =
  run_with(prog, $L.list_vt_cons(arg_text(prog), args), no_arguments())

(* Two texts joined, as one argument *)
#pub fn join_text2 {first_len,second_len:nat | first_len < 4096; second_len < 4096}
  (first: string first_len, second: string second_len): $P.arg_entry

implement join_text2 (first, second) = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, first)
  val () = $B.bput(out, second)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* The current directory, in an array of 4096 bytes: its length *)
#pub fn cwd_length {l:agz} (buffer: !$A.arr(byte, l, 4096)): [k:nat | k <= 4096] int k

implement cwd_length (buffer) =
  case+ $E.cwd_read(buffer, 4096) of
  | ~$R.some(k) => k
  | ~$R.none() => 0

fun _output_contains {l:agz}{output_len:nat | output_len <= 524288}{i:nat | i <= output_len}{needle_len:pos} .<output_len - i>.
  (output_text: !$A.borrow(byte, l, 524288), output_len: int output_len, i: int i, needle: string needle_len): bool =
  if i >= output_len then false
  else if lit_step(output_text, output_len, i, needle) >= 0 then true
  else _output_contains(output_text, output_len, i + 1, needle)

(* Whether the output holds the text; the empty text is always held *)
#pub fn output_has {l:agz}{output_len:nat | output_len <= 524288} {needle_len:nat}
  (output_text: !$A.borrow(byte, l, 524288), output_len: int output_len, needle: string needle_len): bool

implement output_has (output_text, output_len, needle) =
  if text_length(needle) > 0 then _output_contains(output_text, output_len, 0, needle) else true

(* Whether the output lacks the text; the empty text is always lacked *)
#pub fn output_lacks {l:agz}{output_len:nat | output_len <= 524288} {needle_len:nat}
  (output_text: !$A.borrow(byte, l, 524288), output_len: int output_len, needle: string needle_len): bool

implement output_lacks (output_text, output_len, needle) =
  if text_length(needle) > 0 then ~_output_contains(output_text, output_len, 0, needle) else true

(* A path, as the array of 524288 bytes a builder gives and its length *)
#pub vtypedef path_text = [l:agz][k:nat | k < 1000] @($A.arr(byte, l, 524288), int k)

(* first, middle and last joined, as a path *)
#pub fn join_path3 {first_len,middle_len,last_len:nat | first_len < 400; middle_len < 200; last_len < 400}
  (first: string first_len, middle: string middle_len, last: string last_len): path_text

implement join_path3 (first, middle, last) = let
  var out : $B.builder(0) = $B.create()
  val () = $B.bput(out, first)
  val () = $B.bput(out, middle)
  val () = $B.bput(out, last)
  val @(arr, k) = $B.to_arr(out)
in @(arr, k) end

(* A path as one argument *)
#pub fn path_argument (path: path_text): $P.arg_entry

implement path_argument (path) = let
  val @(arr, k) = path
in @(arr, k) end

fun _write_chunks {n:nat}{l:agz}{path_cap:pos}{path_len:nat | path_len <= path_cap; path_len < 524288} .<n>.
  (path_view: !$A.borrow(byte, l, path_cap), path_len: int path_len, chunks: $B.rope_sized_list(n), append: bool): bool =
  case+ chunks of
  | ~$B.rope_sized_nil() => true
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(chunk_frozen, chunk_view) = $A.freeze<byte>(chunk)
      val written = write_file(path_view, path_len, chunk_view, used, append)
      val () = $A.drop<byte>(chunk_frozen, chunk_view)
      val () = $A.free<byte>($A.thaw<byte>(chunk_frozen))
      val rest_written = _write_chunks(path_view, path_len, rest, true)
    in written && rest_written end

(* The rope written to the file at the path (made or emptied first) *)
#pub fn write_rope (path: path_text, text: $B.sized_rope): bool

implement write_rope (path, text) = let
  val @(path_array, path_len) = path
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val written = _write_chunks(path_view, path_len, $B.sized_rope_chunks(text), false)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in written end
