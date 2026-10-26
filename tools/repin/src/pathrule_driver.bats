(* pathrule_driver -- `repin paths-check` and `repin members-check` (bats-lang/repository-
   prototype#466). Keyword: repin path rule.

   The paths file and the tar's listing are streams, read a byte at a time into one line of
   at most 8192 bytes, so a file of any size is read. Every loop ends on the end of the file;
   what makes it total is a fuel of three ints with a lexicographic metric (fuel.bats), 2^93 - 1
   units at the base 2147483647, a platform assumption (an off_t has 63 bits) and not a proof
   that no stream is longer. A fuel that is gone is a refusal in every loop and read, never an
   acceptance: ten places of the code have that branch (the lines of the five loops, the reads
   of their five calls of _next_line), and `which` of check_paths_with_fuel and
   check_members_with_fuel gives one of them a small fuel for a test, the others the full one.
   The member count is limited to 100000 and the sizes are exact digit strings (sizes.bats).
   The paths file is read again for each member (is the name under a listed path?) and the
   listing for each listed path (is it a member?), so no list of either is held. A name or a
   path over 8192 bytes is refused: a tree under a listed directory can have member names
   that long, the rule of the Python accepts them and its write then fails with ENAMETOOLONG,
   so the run is red in both and nothing is committed. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use file as F
#use result as R

staload "fuel.sats"
staload "pathrule.sats"
staload "sizes.sats"
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

fn _fuel_message (message: !$B.sized_rope): void =
  $B.sized_rope_bput(message, "::error::the stream is longer than the fuel\n")

(* ============================================================
   The fuel of a loop
   ============================================================ *)

(* The fuel of the place numbered slot: the small fuel (tb, sa, sb, sc) of a test when
   `which` names that place, else the full one. The places: 1 to 5 the lines of _scan_paths,
   _members_loop, _held_loop, _holds_loop, _under_loop; 6 to 10 the reads of their calls of
   _next_line. *)
fn _quad {w:int | 0 <= w; w <= 10}{slot:int}{tb:pos}{sa,sb,sc:nat}
  (w: int w, slot: int slot, tb: int tb, sa: int sa, sb: int sb, sc: int sc)
  : [base:pos][a,b,c:nat] @(int base, int a, int b, int c) =
  if w = slot then @(tb, sa, sb, sc)
  else @(2147483647, 2147483647, 2147483647, 2147483647)

(* ============================================================
   One line
   ============================================================ *)

(* The next line of the reader, without its newline, in line[0, k): k; -1 at the end of the
   file; -2 when the line is longer than 8192 bytes (it is read to its end and dropped); -3
   when the fuel of the reads is gone. The last line may have no newline. *)
fun _next_line {lb,ob:agz}{base:pos}{a,b,c:nat}{len:nat | len <= 8192} .<a, b, c>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: !$A.arr(byte, lb, 16392),
   base: int base, a: int a, b: int b, c: int c, len: int len, over: bool)
  : [k:int | ~3 <= k; k <= 8192] int k =
  if is_gone(a, b, c) then ~3
  else let
    val @(a2, b2, c2) = spend(base, a, b, c)
  in
    case+ $F.buf_read(reader, one, 1) of
    | ~$R.none() => (if over then ~2 else if len > 0 then len else ~1)
    | ~$R.some(_) =>
      if byte2int0($A.get<byte>(one, 0)) = 10 then (if over then ~2 else len)
      else if len >= 8192 then _next_line(reader, one, line, base, a2, b2, c2, len, true)
      else let
        val () = $A.set<byte>(line, len, $A.get<byte>(one, 0))
      in _next_line(reader, one, line, base, a2, b2, c2, len + 1, over) end
  end

(* ============================================================
   The paths
   ============================================================ *)

(* Each line of the paths stream: 0 when there is a path and none is refused, 1 when there is
   no path, 2 when a path is refused, 3 when a line is over 8192 bytes, 4 when a fuel is gone;
   the refusal is appended to message *)
fun _scan_paths {lb,ob:agz}{w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  {lbase:pos}{la,lb2,lc:nat} .<la, lb2, lc>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 16392),
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc,
   lbase: int lbase, la: int la, lb2: int lb2, lc: int lc, seen: int,
   message: !$B.sized_rope): @($A.arr(byte, lb, 16392), int) =
  if is_gone(la, lb2, lc) then let val () = _fuel_message(message) in @(line, 4) end
  else let
    val @(a2, b2, c2) = spend(lbase, la, lb2, lc)
    val @(bbase, ba, bb, bc) = _quad(w, 6, tb, sa, sb, sc)
    val n = _next_line(reader, one, line, bbase, ba, bb, bc, 0, false)
  in
    if n = ~3 then let val () = _fuel_message(message) in @(line, 4) end
    else if n = ~1 then @(line, (if seen > 0 then 0 else 1))
    else if n = ~2 then let
      val () = $B.sized_rope_bput(message,
        "::error::a path of repin-paths is longer than 8192 bytes: the test -e of job repin fails for it (ENAMETOOLONG)\n")
    in @(line, 3) end
    else if n <= 0 then
      _scan_paths(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2, seen, message)
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
      else _scan_paths(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2, seen + 1, message)
    end
  end

(* The paths file named name[0, len) checked by the rule: 0 when it has a path and none is
   refused, else 1 with the refusal in message *)
fn _paths_pass {nl:agz}{nn:pos}{len:nat | len <= nn; len < 524288}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  (name: !$A.borrow(byte, nl, nn), len: int len, w: int w, tb: int tb, sa: int sa, sb: int sb,
   sc: int sc, message: !$B.sized_rope): int =
  case+ _open_reader(name, len) of
  | ~$R.none() => 1
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(16392)
      val @(lbase, la, lb, lc) = _quad(w, 1, tb, sa, sb, sc)
      val @(line, code) = _scan_paths(reader, one, line, w, tb, sa, sb, sc, lbase, la, lb, lc, 0,
        message)
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
   stream searched. 1 yes, 0 no, 2 a fuel is gone (said in message). *)
fun _under_loop {lb,ob,nl:agz}{nn:pos}{name_stop:nat | name_stop <= nn}
  {name_start:nat | name_start <= name_stop}{w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  {lbase:pos}{la,lb2,lc:nat} .<la, lb2, lc>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 16392),
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc,
   lbase: int lbase, la: int la, lb2: int lb2, lc: int lc,
   name: !$A.borrow(byte, nl, nn), name_start: int name_start, name_stop: int name_stop,
   message: !$B.sized_rope): @($A.arr(byte, lb, 16392), int) =
  if is_gone(la, lb2, lc) then let val () = _fuel_message(message) in @(line, 2) end
  else let
    val @(a2, b2, c2) = spend(lbase, la, lb2, lc)
    val @(bbase, ba, bb, bc) = _quad(w, 10, tb, sa, sb, sc)
    val n = _next_line(reader, one, line, bbase, ba, bb, bc, 0, false)
  in
    if n = ~3 then let val () = _fuel_message(message) in @(line, 2) end
    else if n = ~1 then @(line, 0)
    else if n <= 0 then _under_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2,
      name, name_start, name_stop, message)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val hit = name_under_path(name, name_start, name_stop, view, 0, n)
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if hit then @(line, 1)
      else _under_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2,
        name, name_start, name_stop, message)
    end
  end

fn _name_is_under_a_path {nl,pl:agz}{nn,pn:pos}{name_stop:nat | name_stop <= nn}
  {name_start:nat | name_start <= name_stop}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  (paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   name: !$A.borrow(byte, nl, nn), name_start: int name_start, name_stop: int name_stop,
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc, message: !$B.sized_rope): int =
  case+ _open_reader(paths_name, paths_len) of
  | ~$R.none() => 0
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(16392)
      val @(lbase, la, lb, lc) = _quad(w, 5, tb, sa, sb, sc)
      val @(line, found) = _under_loop(reader, one, line, w, tb, sa, sb, sc, lbase, la, lb, lc,
        name, name_start, name_stop, message)
      val () = $A.free<byte>(line)
      val () = $A.free<byte>(one)
      val () = _close_reader(reader)
    in found end

(* One line of the listing, line[0, n): the code and the span of the size (empty unless the
   member is a regular file, the only kind whose size the Python adds): 0 a member that
   passes, 1 a name (refused), 2 a type, 4 no member, 5 a fuel is gone; the refusal is
   appended to message *)
fn _judge_member {lb,pl:agz}{pn:pos}{n:pos | n <= 8192}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  (view: !$A.borrow(byte, lb, 16392), n: int n,
   paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc, message: !$B.sized_rope)
  : [s,e:nat | s <= e; e <= n] @(int, int s, int e) = let
  val @(kind, size_start, size_stop, name_start, name_stop) = parse_member(view, 0, n)
in
  if kind < 0 then let
    val () = $B.sized_rope_bput(message, "::error::a line of the tar listing that is no member: ")
    val () = $B.sized_rope_copy(message, view, 0, n)
    val () = $B.sized_rope_bput(message, "\n")
  in @(4, 0, 0) end
  else if kind = 2 then let
    val () = $B.sized_rope_bput(message, "::error::a member that is not a regular file or a directory: ")
    val () = $B.sized_rope_copy(message, view, 0, n)
    val () = $B.sized_rope_bput(message, "\n")
  in @(2, 0, 0) end
  else let
    val name_end = member_end(view, kind, name_start, name_stop)
    val refused = path_refused(view, name_start, name_end)
    val under = (if refused then 0
                 else _name_is_under_a_path(paths_name, paths_len, view, name_start, name_end,
                        w, tb, sa, sb, sc, message)): int
  in
    if under = 2 then @(5, 0, 0)
    else if under = 0 then let
      val () = $B.sized_rope_bput(message,
        "::error::a member outside the listed paths or with a refused name: ")
      val () = $B.sized_rope_copy(message, view, name_start, name_end)
      val () = $B.sized_rope_bput(message, "\n")
    in @(1, 0, 0) end
    else if kind = 0 then @(0, size_start, size_stop)
    else @(0, 0, 0)
  end
end

(* Each line of the listing stream: 0 when every member is a regular file or a directory
   that passes (not over the member limit, a name the rule accepts, a listed path or under
   one, the sizes at most the cap); else 1 with the refusal in message. The line array holds
   the room left of the cap after its line region (sizes.bats). *)
fun _members_loop {lb,ob,pl:agz}{pn:pos}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}{lbase:pos}{la,lb2,lc:nat}
  {room_start:nat | 8192 <= room_start; room_start <= 16392} .<la, lb2, lc>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 16392),
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc,
   lbase: int lbase, la: int la, lb2: int lb2, lc: int lc, count: int,
   room_start: int room_start, unlimited: bool,
   paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   message: !$B.sized_rope): @($A.arr(byte, lb, 16392), int) =
  if is_gone(la, lb2, lc) then let val () = _fuel_message(message) in @(line, 1) end
  else let
    val @(a2, b2, c2) = spend(lbase, la, lb2, lc)
    val @(bbase, ba, bb, bc) = _quad(w, 7, tb, sa, sb, sc)
    val n = _next_line(reader, one, line, bbase, ba, bb, bc, 0, false)
  in
    if n = ~3 then let val () = _fuel_message(message) in @(line, 1) end
    else if n = ~1 then @(line, 0)
    else if n = ~2 then let
      val () = $B.sized_rope_bput(message,
        "::error::a name of the tar listing is longer than 8192 bytes: its write fails (ENAMETOOLONG), so the run is red in any case\n")
    in @(line, 1) end
    else if count + 1 > _member_limit() then let
      val () = $B.sized_rope_bput(message, "::error::too many members in the repinned files\n")
    in @(line, 1) end
    else if n <= 0 then let
      val () = $B.sized_rope_bput(message, "::error::a line of the tar listing that is no member: \n")
    in @(line, 1) end
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val @(code, size_start, size_stop) =
        _judge_member(view, n, paths_name, paths_len, w, tb, sa, sb, sc, message)
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if code != 0 then @(line, 1)
      else if unlimited then
        _members_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2, count + 1,
          room_start, unlimited, paths_name, paths_len, message)
      else let
        val @(fits, room_next) = room_take(line, size_start, size_stop, room_start)
      in
        if fits then
          _members_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2, count + 1,
            room_next, unlimited, paths_name, paths_len, message)
        else let
          val () = $B.sized_rope_bput(message, "::error::the repinned files are over repin-max-bytes\n")
        in @(line, 1) end
      end
    end
  end

(* ============================================================
   Every listed path is a member
   ============================================================ *)

(* Whether a member of the listing stream is exactly path[0, path_len): 1 yes, 0 no, 2 a
   fuel is gone (said in message) *)
fun _holds_loop {lb,ob,pl:agz}{pn:pos}{path_len:nat | path_len <= pn}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}{lbase:pos}{la,lb2,lc:nat} .<la, lb2, lc>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 16392),
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc,
   lbase: int lbase, la: int la, lb2: int lb2, lc: int lc,
   path: !$A.borrow(byte, pl, pn), path_len: int path_len, message: !$B.sized_rope)
  : @($A.arr(byte, lb, 16392), int) =
  if is_gone(la, lb2, lc) then let val () = _fuel_message(message) in @(line, 2) end
  else let
    val @(a2, b2, c2) = spend(lbase, la, lb2, lc)
    val @(bbase, ba, bb, bc) = _quad(w, 9, tb, sa, sb, sc)
    val n = _next_line(reader, one, line, bbase, ba, bb, bc, 0, false)
  in
    if n = ~3 then let val () = _fuel_message(message) in @(line, 2) end
    else if n = ~1 then @(line, 0)
    else if n <= 0 then _holds_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2,
      path, path_len, message)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val @(kind, _, _, name_start, name_stop) = parse_member(view, 0, n)
      val same =
        (if kind < 0 || kind = 2 then false
         else let
           val name_end = member_end(view, kind, name_start, name_stop)
         in spans_equal(view, name_start, name_end, path, 0, path_len) end): bool
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if same then @(line, 1)
      else _holds_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2, path, path_len,
        message)
    end
  end

fn _listing_holds {ll,pl:agz}{ln,pn:pos}{listing_len:nat | listing_len <= ln; listing_len < 524288}
  {path_len:nat | path_len <= pn}{w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  (listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   path: !$A.borrow(byte, pl, pn), path_len: int path_len,
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc, message: !$B.sized_rope): int =
  case+ _open_reader(listing_name, listing_len) of
  | ~$R.none() => 0
  | ~$R.some(reader) => let
      val one = $A.alloc<byte>(1)
      val line = $A.alloc<byte>(16392)
      val @(lbase, la, lb, lc) = _quad(w, 4, tb, sa, sb, sc)
      val @(line, found) = _holds_loop(reader, one, line, w, tb, sa, sb, sc, lbase, la, lb, lc,
        path, path_len, message)
      val () = $A.free<byte>(line)
      val () = $A.free<byte>(one)
      val () = _close_reader(reader)
    in found end

(* Each path of the paths stream is a member of the listing: 0, else 1 with the first that is
   not (or the fuel) in message *)
fun _held_loop {lb,ob,ll:agz}{ln:pos}{listing_len:nat | listing_len <= ln; listing_len < 524288}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}{lbase:pos}{la,lb2,lc:nat} .<la, lb2, lc>.
  (reader: !$F.buf_reader, one: !$A.arr(byte, ob, 1), line: $A.arr(byte, lb, 16392),
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc,
   lbase: int lbase, la: int la, lb2: int lb2, lc: int lc,
   listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   message: !$B.sized_rope): @($A.arr(byte, lb, 16392), int) =
  if is_gone(la, lb2, lc) then let val () = _fuel_message(message) in @(line, 1) end
  else let
    val @(a2, b2, c2) = spend(lbase, la, lb2, lc)
    val @(bbase, ba, bb, bc) = _quad(w, 8, tb, sa, sb, sc)
    val n = _next_line(reader, one, line, bbase, ba, bb, bc, 0, false)
  in
    if n = ~3 then let val () = _fuel_message(message) in @(line, 1) end
    else if n = ~1 then @(line, 0)
    else if n <= 0 then _held_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2,
      listing_name, listing_len, message)
    else let
      val @(frozen, view) = $A.freeze<byte>(line)
      val found = _listing_holds(listing_name, listing_len, view, n, w, tb, sa, sb, sc, message)
      val () =
        if found = 0 then let
          val () = $B.sized_rope_bput(message, "::error::the repinned files do not hold ")
          val () = $B.sized_rope_copy(message, view, 0, n)
          val () = $B.sized_rope_bput(message, "\n")
        in () end
        else ()
      val () = $A.drop<byte>(frozen, view)
      val line = $A.thaw<byte>(frozen)
    in
      if found = 1 then
        _held_loop(reader, one, line, w, tb, sa, sb, sc, lbase, a2, b2, c2,
          listing_name, listing_len, message)
      else @(line, 1)
    end
  end

(* The three passes over the files named paths_name and listing_name; the cap is the digits
   cap[cap_start, cap_stop) *)
fn _members_pass {pl,ll,cl:agz}{pn,ln,cn:pos}{paths_len:nat | paths_len <= pn; paths_len < 524288}
  {listing_len:nat | listing_len <= ln; listing_len < 524288}
  {cap_stop:nat | cap_stop <= cn}{cap_start:nat | cap_start <= cap_stop}
  {w:int | 0 <= w; w <= 10}{tb:pos}{sa,sb,sc:nat}
  (paths_name: !$A.borrow(byte, pl, pn), paths_len: int paths_len,
   listing_name: !$A.borrow(byte, ll, ln), listing_len: int listing_len,
   cap: !$A.borrow(byte, cl, cn), cap_start: int cap_start, cap_stop: int cap_stop,
   w: int w, tb: int tb, sa: int sa, sb: int sb, sc: int sc, message: !$B.sized_rope): int =
  if _paths_pass(paths_name, paths_len, w, tb, sa, sb, sc, message) != 0 then 1
  else let
    val members =
      (case+ _open_reader(listing_name, listing_len) of
       | ~$R.none() => 1
       | ~$R.some(reader) => let
           val one = $A.alloc<byte>(1)
           val line = $A.alloc<byte>(16392)
           val @(unlimited, room_start) = room_init(line, cap, cap_start, cap_stop)
           val @(lbase, la, lb, lc) = _quad(w, 2, tb, sa, sb, sc)
           val @(line, code) = _members_loop(reader, one, line, w, tb, sa, sb, sc, lbase, la, lb,
             lc, 0, room_start, unlimited, paths_name, paths_len, message)
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
           val line = $A.alloc<byte>(16392)
           val @(lbase, la, lb, lc) = _quad(w, 3, tb, sa, sb, sc)
           val @(line, code) = _held_loop(reader, one, line, w, tb, sa, sb, sc, lbase, la, lb, lc,
             listing_name, listing_len, message)
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

(* run_paths_check with the fuel of a test: `which` names the place (0 for none, 1 to 10 as
   _quad numbers them) that gets the fuel (base, a, b, c) *)
#pub fn check_paths_with_fuel {args_loc:agz}{args_size:pos}{paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  {w:int | 0 <= w; w <= 10}{base:pos}{a,b,c:nat}
  (args: !$A.borrow(byte, args_loc, args_size), paths_start: int paths_start,
   paths_stop: int paths_stop, message: !$B.sized_rope, w: int w, base: int base, a: int a,
   b: int b, c: int c): int

implement check_paths_with_fuel (args, paths_start, paths_stop, message, w, base, a, b, c) = let
  val @(name_array, name_len) = _name_of(args, paths_start, paths_stop)
  val @(name_frozen, name_view) = $A.freeze<byte>(name_array)
  val status = _paths_pass(name_view, name_len, w, base, a, b, c, message)
  val () = $A.drop<byte>(name_frozen, name_view)
  val () = $A.free<byte>($A.thaw<byte>(name_frozen))
in status end

(* The paths file at args[paths_start, paths_stop) checked by the rule: 0 when it has a path
   and none is refused, else 1 with the refusal in message *)
#pub fn run_paths_check {args_loc:agz}{args_size:pos}{paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  (args: !$A.borrow(byte, args_loc, args_size), paths_start: int paths_start,
   paths_stop: int paths_stop, message: !$B.sized_rope): int

implement run_paths_check (args, paths_start, paths_stop, message) =
  check_paths_with_fuel(args, paths_start, paths_stop, message, 0, 1, 0, 0, 0)

(* run_members_check with the fuel of a test *)
#pub fn check_members_with_fuel {args_loc:agz}{args_size:pos}
  {cap_stop:nat | cap_stop <= args_size}{cap_start:nat | cap_start <= cap_stop}
  {paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  {listing_stop:nat | listing_stop <= args_size}
  {listing_start:nat | listing_start <= listing_stop; listing_stop - listing_start <= 4096}
  {w:int | 0 <= w; w <= 10}{base:pos}{a,b,c:nat}
  (args: !$A.borrow(byte, args_loc, args_size), listing_start: int listing_start,
   listing_stop: int listing_stop, paths_start: int paths_start, paths_stop: int paths_stop,
   cap_start: int cap_start, cap_stop: int cap_stop, message: !$B.sized_rope,
   w: int w, base: int base, a: int a, b: int b, c: int c): int

implement check_members_with_fuel (args, listing_start, listing_stop, paths_start, paths_stop,
  cap_start, cap_stop, message, w, base, a, b, c) =
  if ~digits_only(args, cap_start, cap_stop) then
    let val () = prerrln! ("repin: MAX_BYTES is digits") in 1 end
  else let
    val @(paths_array, paths_len) = _name_of(args, paths_start, paths_stop)
    val @(paths_frozen, paths_view) = $A.freeze<byte>(paths_array)
    val @(listing_array, listing_len) = _name_of(args, listing_start, listing_stop)
    val @(listing_frozen, listing_view) = $A.freeze<byte>(listing_array)
    val status = _members_pass(paths_view, paths_len, listing_view, listing_len,
      args, cap_start, cap_stop, w, base, a, b, c, message)
    val () = $A.drop<byte>(listing_frozen, listing_view)
    val () = $A.free<byte>($A.thaw<byte>(listing_frozen))
    val () = $A.drop<byte>(paths_frozen, paths_view)
    val () = $A.free<byte>($A.thaw<byte>(paths_frozen))
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
  cap_start, cap_stop, message) =
  check_members_with_fuel(args, listing_start, listing_stop, paths_start, paths_stop,
    cap_start, cap_stop, message, 0, 1, 0, 0, 0)
