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

fun _put_range {l:agz}{n:pos}{i,stop:nat | i <= stop; stop <= n}
  {used:nat | used + (stop - i) <= 524288} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, stop: int stop,
   out: !$B.builder(used) >> $B.builder(used + (stop - i))): void =
  if i >= stop then ()
  else let
    val () = $B.put_char(out, $AR.low_byte(byte2int0($A.read<byte>(bytes, i))))
  in _put_range(bytes, i + 1, stop, out) end

(* bytes[start, stop) appended to out; the builder's length after is in its
   type *)
#pub fn put_range {l:agz}{n:pos}{start,stop:nat | start <= stop; stop <= n}
  {used:nat | used + (stop - start) <= 524288}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop,
   out: !$B.builder(used) >> $B.builder(used + (stop - start))): void

implement put_range (bytes, start, stop, out) = _put_range(bytes, start, stop, out)

fun _print_range {l:agz}{n:pos}{i,stop:nat | i <= stop; stop <= n} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, stop: int stop): void =
  if i >= stop then ()
  else let
    val () = print_char(int2char0(byte2int0($A.read<byte>(bytes, i))))
  in _print_range(bytes, i + 1, stop) end

(* bytes[start, stop) to standard output *)
#pub fn print_range {l:agz}{n:pos}{start,stop:nat | start <= stop; stop <= n}
  (bytes: !$A.borrow(byte, l, n), start: int start, stop: int stop): void

implement print_range (bytes, start, stop) = _print_range(bytes, start, stop)

fun _find_byte {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, wanted: int)
  : [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if byte2int0($A.read<byte>(bytes, i)) = wanted then i
  else _find_byte(bytes, limit, i + 1, wanted)

(* The first place at or after start of bytes[0, limit) where the byte is
   wanted, or limit *)
#pub fn find_byte {l:agz}{n:pos}{limit:nat | limit <= n}{start:nat | start <= limit}
  (bytes: !$A.borrow(byte, l, n), limit: int limit, start: int start, wanted: int)
  : [j:nat | start <= j; j <= limit] int j

implement find_byte (bytes, limit, start, wanted) = _find_byte(bytes, limit, start, wanted)

fun _lit_from {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit}{literal_len:nat}
  {at:nat | at <= literal_len} .<literal_len - at>.
  (bytes: !$A.borrow(byte, l, n), limit: int limit, i: int i, literal: string literal_len,
   literal_len: int literal_len, at: int at): bool =
  if at >= literal_len then true
  else if i >= limit then false
  else if byte2int0($A.read<byte>(bytes, i)) = char2int0(string_get_at(literal, at)) then
    _lit_from(bytes, limit, i + 1, literal, literal_len, at + 1)
  else false

(* Whether bytes[line_start, line_stop) are exactly the text literal *)
#pub fn span_is {l:agz}{n:pos}{line_stop:nat | line_stop <= n}
  {line_start:nat | line_start <= line_stop}{literal_len:nat}
  (bytes: !$A.borrow(byte, l, n), line_start: int line_start, line_stop: int line_stop,
   literal: string literal_len): bool

implement span_is (bytes, line_start, line_stop, literal) =
  if line_stop - line_start = g1u2i(string1_length(literal)) then
    _lit_from(bytes, line_stop, line_start, literal, g1u2i(string1_length(literal)), 0)
  else false

(* Reads an open file to its end into out. A chunk that would take the
   builder past its capacity is not appended (nothing is cut): the outcome is
   Read_too_long. Each chunk is at least one byte, so the room left is the
   metric. *)
fun _drain {used:nat | used <= 524288} .<524288 - used>.
  (fd: !$F.fd, out: !$B.builder(used) >> $B.builder_v): read_end = let
  val chunk = $A.alloc<byte>(4096)
in
  case+ $F.file_read(fd, chunk, 4096) of
  | ~$R.err(_) => let val () = $A.free<byte>(chunk) in Read_failed() end
  | ~$R.ok(count) =>
    if count <= 0 then let val () = $A.free<byte>(chunk) in Read_whole() end
    else if $B.length(out) + count > 524288 then
      let val () = $A.free<byte>(chunk) in Read_too_long() end
    else let
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val () = _put_range(view, 0, count, out)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
    in _drain(fd, out) end
end

fun _copy_path {l,other_loc:agz}{n:pos}{path_len:nat | path_len <= n}
  {capacity:pos | path_len < capacity}{i:nat | i <= path_len} .<path_len - i>.
  (path: !$A.borrow(byte, l, n), path_len: int path_len,
   destination: !$A.arr(byte, other_loc, capacity), i: int i): void =
  if i >= path_len then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(path, i))
  in _copy_path(path, path_len, destination, i + 1) end

(* The path path[0, path_len) opened for reading; the path is copied into an array of
   its own length and a zero, which file_open takes. *)
fn _open_read {l:agz}{n:pos}{path_len:nat | path_len <= n; path_len < 524288}
  (path: !$A.borrow(byte, l, n), path_len: int path_len): $R.result($F.fd, $F.io_error) = let
  val path_copy = $A.alloc<byte>(path_len + 1)
  val () = _copy_path(path, path_len, path_copy, 0)
  val @(frozen, view) = $A.freeze<byte>(path_copy)
  val opened = $F.file_open(view, path_len + 1, $F.ReadOnly(), $F.OpenExisting(), 0)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in opened end

(* The bytes of the file at the path path[0, path_len), read into out: how the read
   ended, and the words of the error when it failed (an empty text
   otherwise) *)
#pub fn read_file {l:agz}{n:pos}{path_len:nat | path_len <= n; path_len < 524288}
  (path: !$A.borrow(byte, l, n), path_len: int path_len,
   out: !$B.builder(0) >> $B.builder_v): @(read_end, string)

implement read_file (path, path_len, out) =
  case+ _open_read(path, path_len) of
  | ~$R.err(failure) => @(Read_failed(), $F.io_error_text(failure))
  | ~$R.ok(fd) => let
      val ended = _drain(fd, out)
      val () = $R.discard<int><$F.io_error>($F.file_close(fd))
    in @(ended, "") end

fun _print_chunks {chunk_count:nat} .<chunk_count>.
  (chunks: $B.rope_sized_list(chunk_count)): void =
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
