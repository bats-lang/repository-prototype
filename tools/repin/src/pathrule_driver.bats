(* pathrule_driver -- `repin paths-check` and `repin members-check` (bats-lang/repository-
   prototype#466). Keyword: repin path rule.

   The paths file and the tar's listing are streams, read a byte at a time into one line of
   at most 8192 bytes, so a file of any size is read (the member count and the sizes are
   what limit a tar, as in the workflow: at most 100000 members, the sizes at most the cap).
   A name or a path longer than 8192 bytes is refused: PATH_MAX is 4096 on Linux, so no file
   has such a path and the write of it would fail in any case. The paths file is read again for
   each member (is the name under a listed path?) and the listing for each listed path (is it
   a member?), so no list of either is held. A file is read for at most 2147483647 bytes (the
   fuel that ends each loop); a longer one is read as far as that. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use file as F
#use result as R

staload "pathrule.sats"
staload "support.sats"

(* The most members a tar may have, as the workflow's Python states it *)
fn _member_limit (): int = 100000

fn _close_reader (reader: $F.buf_reader): void =
  $R.discard<int><$F.io_error>($F.buf_reader_close(reader))

(* The file named name[0, len), opened as a reader; none (said on standard error) when it
   cannot be read *)
fn _open_reader {nl:agz}{nn:pos}{len:nat | len <= nn; len < 524288}
  (name: !$A.borrow(byte, nl, nn), len: int len): $R.option($F.buf_reader) =
  case+ open_read_file(name, len) of
  | ~$R.err(failure) => let
      val () = prerrln! ("repin: cannot read a file: ", $F.io_error_text(failure))
    in $R.none() end
  | ~$R.ok(fd) => $R.some($F.buf_reader_create(fd))

(* The next line of the reader, without its newline, in line[0, k): k; -1 at the end of the
   file; -2 when the line is longer than 8192 bytes (it is read to its end and dropped). The
   last line may have no newline. *)
fun _next_line {lb,ob:agz}{fuel:nat}{len:nat | len <= 8192} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: !$A.arr(byte, lb, 8192),
   fuel: int fuel, len: int len, over: bool): [k:int | ~2 <= k; k <= 8192] int k =
  if fuel <= 0 then (if over then ~2 else if len > 0 then len else ~1)
  else
    (case+ $F.buf_read(reader, one, 1) of
     | ~$R.none() => (if over then ~2 else if len > 0 then len else ~1)
     | ~$R.some(_) =>
       if byte2int0($A.get<byte>(one, 0)) = 10 then (if over then ~2 else len)
       else if len >= 8192 then _next_line(reader, one, line, fuel - 1, len, true)
       else let
         val () = $A.set<byte>(line, len, $A.get<byte>(one, 0))
       in _next_line(reader, one, line, fuel - 1, len + 1, over) end)

(* ============================================================
   The paths
   ============================================================ *)

(* Each line of the paths stream: 0 when there is a path and none is refused, 1 when there is
   no path, 2 when a path is refused, 3 when a line is over 8192 bytes; the refusal is
   appended to message *)
fun _scan_paths {lb,ob:agz}{fuel:nat} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 8192),
   fuel: int fuel, seen: int, message: !$B.sized_rope): @($A.arr(byte, lb, 8192), int) =
  if fuel <= 0 then @(line, (if seen > 0 then 0 else 1))
  else let
    val n = _next_line(reader, one, line, 2147483647, 0, false)
  in
    if n = ~1 then @(line, (if seen > 0 then 0 else 1))
    else if n = ~2 then let
      val () = $B.sized_rope_bput(message,
        "::error::a path of repin-paths is longer than 8192 bytes: no file has such a path\n")
    in @(line, 3) end
    else if n <= 0 then _scan_paths(reader, one, line, fuel - 1, seen, message)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val refused = path_refused(view, 0, n)
      val () =
        if refused then let
          val () = $B.sized_rope_bput(message, "::error::repin-paths names a path that is refused: ")
          val () = $B.sized_rope_copy(message, view, 0, n)
          val () = $B.sized_rope_bput(message, "\n")
        in () end
        else ()
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if refused then @(line, 2)
      else _scan_paths(reader, one, line, fuel - 1, seen + 1, message)
    end
  end

(* The paths file named name[0, len) checked by the rule: 0 when it has a path and none is
   refused, else 1 with the refusal in message *)
fn _paths_pass {nl:agz}{nn:pos}{len:nat | len <= nn; len < 524288}
  (name: !$A.borrow(byte, nl, nn), len: int len, message: !$B.sized_rope): int =
  case+ _open_reader(name, len) of
  | ~$R.none() => 1
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(8192)
      val @(line, code) = _scan_paths(reader, one, line, 2147483647, 0, message)
      val () = $A.free<byte>(line)
      val () = $A.free<byte>(one)
      val () = _close_reader(reader)
      val () =
        if code = 1 then
          $B.sized_rope_bput(message, "::error::repin-paths is empty: nothing would be committed\n")
        else ()
    in if code = 0 then 0 else 1 end

(* ============================================================
   The members
   ============================================================ *)

(* Whether the name name[name_start, name_stop) is a listed path or under one: the paths
   stream searched *)
fun _under_loop {lb,ob,nl:agz}{nn:pos}{name_stop:nat | name_stop <= nn}
  {name_start:nat | name_start <= name_stop}{fuel:nat} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 8192),
   fuel: int fuel, name: !$A.borrow(byte, nl, nn), name_start: int name_start,
   name_stop: int name_stop): @($A.arr(byte, lb, 8192), bool) =
  if fuel <= 0 then @(line, false)
  else let
    val n = _next_line(reader, one, line, 2147483647, 0, false)
  in
    if n = ~1 then @(line, false)
    else if n <= 0 then _under_loop(reader, one, line, fuel - 1, name, name_start, name_stop)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val hit = name_under_path(name, name_start, name_stop, view, 0, n)
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if hit then @(line, true)
      else _under_loop(reader, one, line, fuel - 1, name, name_start, name_stop)
    end
  end

fn _name_is_under_a_path {nl,pl:agz}{nn,pn:pos}{name_stop:nat | name_stop <= nn}
  {name_start:nat | name_start <= name_stop}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  (paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   name: !$A.borrow(byte, nl, nn), name_start: int name_start, name_stop: int name_stop): bool =
  case+ _open_reader(paths_name, paths_len) of
  | ~$R.none() => false
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(8192)
      val @(line, hit) = _under_loop(reader, one, line, 2147483647, name, name_start, name_stop)
      val () = $A.free<byte>(line)
      val () = $A.free<byte>(one)
      val () = _close_reader(reader)
    in hit end

(* The code of one line of the listing, line[0, n), with the refusal appended to message:
   0 a member that passes, the size in size_out is its size; 1 a name; 2 a type; 4 no member *)
fn _judge_member {lb,pl:agz}{pn:pos}{n:pos | n <= 8192}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  (view: !$A.borrow(byte, lb, 8192), n: int n,
   paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   message: !$B.sized_rope): @(int, lint) = let
  val @(kind, size, name_start, name_stop) = parse_member(view, 0, n)
in
  if kind < 0 then let
    val () = $B.sized_rope_bput(message, "::error::a line of the tar listing that is no member: ")
    val () = $B.sized_rope_copy(message, view, 0, n)
    val () = $B.sized_rope_bput(message, "\n")
  in @(4, 0L) end
  else if kind = 2 then let
    val () = $B.sized_rope_bput(message, "::error::a member that is not a regular file or a directory: ")
    val () = $B.sized_rope_copy(message, view, 0, n)
    val () = $B.sized_rope_bput(message, "\n")
  in @(2, 0L) end
  else let
    val name_end = member_end(view, kind, name_start, name_stop)
    val refused = path_refused(view, name_start, name_end)
    val outside = (if refused then true
                   else ~_name_is_under_a_path(paths_name, paths_len, view, name_start, name_end)): bool
  in
    if outside then let
      val () = $B.sized_rope_bput(message,
        "::error::a member outside the listed paths or with a refused name: ")
      val () = $B.sized_rope_copy(message, view, name_start, name_end)
      val () = $B.sized_rope_bput(message, "\n")
    in @(1, 0L) end
    else @(0, size)
  end
end

(* Each line of the listing stream: 0 when every member is a regular file or a directory
   that passes (not over the member limit, a name the rule accepts, a listed path or under
   one, the sizes at most the cap); else 1 with the refusal in message *)
fun _members_loop {lb,ob,pl:agz}{pn:pos}{paths_len:nat | paths_len <= pn; paths_len < 524288}{fuel:nat} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 8192),
   fuel: int fuel, count: int, total: lint, cap: lint,
   paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   message: !$B.sized_rope): @($A.arr(byte, lb, 8192), int) =
  if fuel <= 0 then @(line, 0)
  else let
    val n = _next_line(reader, one, line, 2147483647, 0, false)
  in
    if n = ~1 then @(line, 0)
    else if n = ~2 then let
      val () = $B.sized_rope_bput(message,
        "::error::a name of the tar listing is longer than 8192 bytes: no file has such a path\n")
    in @(line, 1) end
    else if count + 1 > _member_limit() then let
      val () = $B.sized_rope_bput(message, "::error::too many members in the repinned files\n")
    in @(line, 1) end
    else if n <= 0 then let
      val () = $B.sized_rope_bput(message, "::error::a line of the tar listing that is no member: \n")
    in @(line, 1) end
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val @(code, size) = _judge_member(view, n, paths_name, paths_len, message)
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if code != 0 then @(line, 1)
      else if total + size > cap then let
        val () = $B.sized_rope_bput(message, "::error::the repinned files are over repin-max-bytes\n")
      in @(line, 1) end
      else _members_loop(reader, one, line, fuel - 1, count + 1, total + size, cap,
        paths_name, paths_len, message)
    end
  end

(* ============================================================
   Every listed path is a member
   ============================================================ *)

(* Whether a member of the listing stream is exactly path[0, path_len) *)
fun _holds_loop {lb,ob,pl:agz}{pn:pos}{path_len:nat | path_len <= pn}{fuel:nat} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 8192),
   fuel: int fuel, path: !$A.borrow(byte, pl, pn), path_len: int path_len)
  : @($A.arr(byte, lb, 8192), bool) =
  if fuel <= 0 then @(line, false)
  else let
    val n = _next_line(reader, one, line, 2147483647, 0, false)
  in
    if n = ~1 then @(line, false)
    else if n <= 0 then _holds_loop(reader, one, line, fuel - 1, path, path_len)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val @(kind, _, name_start, name_stop) = parse_member(view, 0, n)
      val same =
        (if kind < 0 || kind = 2 then false
         else let
           val name_end = member_end(view, kind, name_start, name_stop)
         in spans_equal(view, name_start, name_end, path, 0, path_len) end): bool
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if same then @(line, true) else _holds_loop(reader, one, line, fuel - 1, path, path_len)
    end
  end

fn _listing_holds {ll,pl:agz}{ln,pn:pos}{listing_len:nat | listing_len <= ln; listing_len < 524288}
  {path_len:nat | path_len <= pn}
  (listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   path: !$A.borrow(byte, pl, pn), path_len: int path_len): bool =
  case+ _open_reader(listing_name, listing_len) of
  | ~$R.none() => false
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(8192)
      val @(line, found) = _holds_loop(reader, one, line, 2147483647, path, path_len)
      val () = $A.free<byte>(line)
      val () = $A.free<byte>(one)
      val () = _close_reader(reader)
    in found end

(* Each path of the paths stream is a member of the listing: 0, else 1 with the first that is
   not, in message *)
fun _held_loop {lb,ob,ll:agz}{ln:pos}{listing_len:nat | listing_len <= ln; listing_len < 524288}{fuel:nat} .<fuel>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 8192),
   fuel: int fuel, listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   message: !$B.sized_rope): @($A.arr(byte, lb, 8192), int) =
  if fuel <= 0 then @(line, 0)
  else let
    val n = _next_line(reader, one, line, 2147483647, 0, false)
  in
    if n = ~1 then @(line, 0)
    else if n <= 0 then _held_loop(reader, one, line, fuel - 1, listing_name, listing_len, message)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val found = _listing_holds(listing_name, listing_len, view, n)
      val () =
        if found then ()
        else let
          val () = $B.sized_rope_bput(message, "::error::the repinned files do not hold ")
          val () = $B.sized_rope_copy(message, view, 0, n)
          val () = $B.sized_rope_bput(message, "\n")
        in () end
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if found then _held_loop(reader, one, line, fuel - 1, listing_name, listing_len, message)
      else @(line, 1)
    end
  end

(* The three passes over the files named paths_name and listing_name *)
fn _members_pass {pl,ll:agz}{pn,ln:pos}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  {listing_len:nat | listing_len <= ln; listing_len < 524288}
  (paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   cap: lint, message: !$B.sized_rope): int =
  if _paths_pass(paths_name, paths_len, message) != 0 then 1
  else let
    val members =
      (case+ _open_reader(listing_name, listing_len) of
       | ~$R.none() => 1
       | ~$R.some(reader) => let
           val one = $A.alloc<byte>(1)
           val line = $A.alloc<byte>(8192)
           val @(line, code) = _members_loop(reader, one, line, 2147483647, 0, 0L, cap,
             paths_name, paths_len, message)
           val () = $A.free<byte>(line)
           val () = $A.free<byte>(one)
           val () = _close_reader(reader)
         in code end): int
  in
    if members != 0 then 1
    else
      (case+ _open_reader(paths_name, paths_len) of
       | ~$R.none() => 1
       | ~$R.some(reader) => let
           val one = $A.alloc<byte>(1)
           val line = $A.alloc<byte>(8192)
           val @(line, code) = _held_loop(reader, one, line, 2147483647, listing_name,
             listing_len, message)
           val () = $A.free<byte>(line)
           val () = $A.free<byte>(one)
           val () = _close_reader(reader)
         in code end)
  end

(* args[start, stop) copied into an array of its own, for a file name *)
fn _name_of {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop; stop - start <= 4096}
  (args: !$A.borrow(byte, l, n), start: int start, stop: int stop)
  : [l2:agz] @($A.arr(byte, l2, 524288), int (stop - start)) = let
  var name : $B.builder(0) = $B.create()
  val () = put_range(args, start, stop, name)
  val @(array, used) = $B.to_arr(name)
in @(array, used) end

(* The paths file at args[paths_start, paths_stop) checked by the rule: 0 when it has a path
   and none is refused, else 1 with the refusal in message *)
#pub fn run_paths_check {args_loc:agz}{args_size:pos}{paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  (args: !$A.borrow(byte, args_loc, args_size), paths_start: int paths_start,
   paths_stop: int paths_stop, message: !$B.sized_rope): int

implement run_paths_check (args, paths_start, paths_stop, message) = let
  val @(name_array, name_len) = _name_of(args, paths_start, paths_stop)
  val @(name_frozen, name_view) = $A.freeze<byte>(name_array)
  val status = _paths_pass(name_view, name_len, message)
  val () = $A.drop<byte>(name_frozen, name_view)
  val () = $A.free<byte>($A.thaw<byte>(name_frozen))
in status end

(* The tar listing at args[listing_start, listing_stop) checked against the paths file and the
   cap in digits at args[cap_start, cap_stop): 0 when it passes, else 1 with the refusal in
   message *)
#pub fn run_members_check {args_loc:agz}{args_size:pos}
  {cap_stop:nat | cap_stop <= args_size}{cap_start:nat | cap_start <= cap_stop}
  {paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  {listing_stop:nat | listing_stop <= args_size}
  {listing_start:nat | listing_start <= listing_stop; listing_stop - listing_start <= 4096}
  (args: !$A.borrow(byte, args_loc, args_size), listing_start: int listing_start,
   listing_stop: int listing_stop, paths_start: int paths_start, paths_stop: int paths_stop,
   cap_start: int cap_start, cap_stop: int cap_stop, message: !$B.sized_rope): int

implement run_members_check (args, listing_start, listing_stop, paths_start, paths_stop,
  cap_start, cap_stop, message) = let
  val @(cap_ok, cap) = parse_size(args, cap_start, cap_stop)
in
  if ~cap_ok then let val () = prerrln! ("repin: MAX_BYTES is digits") in 1 end
  else let
    val @(paths_array, paths_len) = _name_of(args, paths_start, paths_stop)
    val @(paths_frozen, paths_view) = $A.freeze<byte>(paths_array)
    val @(listing_array, listing_len) = _name_of(args, listing_start, listing_stop)
    val @(listing_frozen, listing_view) = $A.freeze<byte>(listing_array)
    val status = _members_pass(paths_view, paths_len, listing_view, listing_len, cap, message)
    val () = $A.drop<byte>(listing_frozen, listing_view)
    val () = $A.free<byte>($A.thaw<byte>(listing_frozen))
    val () = $A.drop<byte>(paths_frozen, paths_view)
    val () = $A.free<byte>($A.thaw<byte>(paths_frozen))
  in status end
end
