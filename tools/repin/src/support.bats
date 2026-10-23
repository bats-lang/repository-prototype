(* support -- bytes and files for repin (bats-lang/repository-prototype#410).
   Keyword: repin bounds.

   A file is read whole into a builder, so a text of repin is at most
   524288 bytes; a file that does not fit is the outcome Read_too_long, never
   a cut one. repin reads no YAML and makes no network call: what is here is
   bytes and files. The reading is the pin audit's (tools/pin-audit), which
   is a package of its own and shares no module with this one. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use result as R

(* How reading a file ended: it all fit, it did not fit the 524288-byte
   buffer, or a read failed. Every caller matches all three (case+). *)
#pub datatype read_end =
  | Read_whole
  | Read_too_long
  | Read_failed

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

implement put_range (b, i, k, out) = _put_range(b, i, k, out)

fun _print_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n} .<k - i>.
  (b: !$A.borrow(byte, l, n), i: int i, k: int k): void =
  if i >= k then ()
  else let
    val () = print_char(int2char0(byte2int0($A.read<byte>(b, i))))
  in _print_range(b, i + 1, k) end

(* b[i, k) to standard output *)
#pub fn print_range {l:agz}{n:pos}{i,k:nat | i <= k; k <= n}
  (b: !$A.borrow(byte, l, n), i: int i, k: int k): void

implement print_range (b, i, k) = _print_range(b, i, k)

fun _find_byte {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k} .<k - i>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, stop: int): [j:nat | i <= j; j <= k] int j =
  if i >= k then i
  else if byte2int0($A.read<byte>(b, i)) = stop then i
  else _find_byte(b, k, i + 1, stop)

(* The first place at or after i of b[0, k) where the byte is stop, or k *)
#pub fn find_byte {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, stop: int): [j:nat | i <= j; j <= k] int j

implement find_byte (b, k, i, stop) = _find_byte(b, k, i, stop)

fun _lit_from {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{literal_len:nat}
  {m:nat | m <= literal_len} .<literal_len - m>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, literal: string literal_len,
   literal_len: int literal_len, m: int m): bool =
  if m >= literal_len then true
  else if i >= k then false
  else if byte2int0($A.read<byte>(b, i)) = char2int0(string_get_at(literal, m)) then
    _lit_from(b, k, i + 1, literal, literal_len, m + 1)
  else false

(* Whether the bytes b[line_start, line_stop) are exactly the text literal *)
#pub fn span_is {l:agz}{n:pos}{line_stop:nat | line_stop <= n}
  {line_start:nat | line_start <= line_stop}{literal_len:nat}
  (b: !$A.borrow(byte, l, n), line_start: int line_start, line_stop: int line_stop,
   literal: string literal_len): bool

implement span_is (b, line_start, line_stop, literal) =
  if line_stop - line_start = g1u2i(string1_length(literal)) then
    _lit_from(b, line_stop, line_start, literal, g1u2i(string1_length(literal)), 0)
  else false

(* Reads an open file to its end into out. A chunk that would take the
   builder past its capacity is not appended (nothing is cut): the outcome is
   Read_too_long. Each chunk is at least one byte, so the room left is the
   metric. *)
fun _drain {m:nat | m <= 524288} .<524288 - m>.
  (fd: !$F.fd, out: !$B.builder(m) >> $B.builder_v): read_end = let
  val chunk = $A.alloc<byte>(4096)
in
  case+ $F.file_read(fd, chunk, 4096) of
  | ~$R.err(_) => let val () = $A.free<byte>(chunk) in Read_failed() end
  | ~$R.ok(k) =>
    if k <= 0 then let val () = $A.free<byte>(chunk) in Read_whole() end
    else if $B.length(out) + k > 524288 then
      let val () = $A.free<byte>(chunk) in Read_too_long() end
    else let
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val () = _put_range(view, 0, k, out)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
    in _drain(fd, out) end
end

fun _copy_path {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m < capacity}
  {i:nat | i <= m} .<m - i>.
  (p: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity),
   i: int i): void =
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

fun _print_chunks {k:nat} .<k>. (chunks: $B.rope_sized_list(k)): void =
  case+ chunks of
  | ~$B.rope_sized_nil() => ()
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val () = _print_range(view, 0, used)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
    in _print_chunks(rest) end

(* The rope's text to standard output *)
#pub fn print_rope (text: $B.sized_rope): void

implement print_rope (text) = _print_chunks($B.sized_rope_chunks(text))

(* The rope's text dropped *)
#pub fn discard_rope (text: $B.sized_rope): void

implement discard_rope (text) = $B.rope_sized_list_free($B.sized_rope_chunks(text))
