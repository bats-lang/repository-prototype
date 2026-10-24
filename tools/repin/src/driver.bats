(* driver -- `repin actions` over a directory (bats-lang/repository-prototype#411).
   Keyword: repin actions.

   The workflow files of a directory (the names ending .yml or .yaml, in the order of
   their names) are read whole, so a file is at most 524288 bytes, and the releases file
   likewise. Every file is first rewritten in memory; only when none has a refused line
   (actions.bats) is any file written, and only a file with a moved pin is, over itself
   (its permission bits stay). The move records of the pins examined, in order, are
   appended to the records the caller prints. *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use file as F
#use result as R

staload "actions.sats"
staload "records.sats"
staload "support.sats"

fun _err_range {l:agz}{n:pos}{i,stop:nat | i <= stop; stop <= n} .<stop - i>.
  (bytes: !$A.borrow(byte, l, n), i: int i, stop: int stop): void =
  if i >= stop then ()
  else let
    val () = prerr_char(int2char0(byte2int0($A.read<byte>(bytes, i))))
  in _err_range(bytes, i + 1, stop) end

(* The start of line number target (from 1) of text[0, text_len), searching from the
   line that starts at i and is number number *)
fun _line_start {l:agz}{n:pos}{text_len:nat | text_len <= n}{i:nat | i <= text_len} .<text_len - i>.
  (text: !$A.borrow(byte, l, n), text_len: int text_len, i: int i, number: int, target: int)
  : [k:nat | k <= text_len] int k =
  if number >= target then i
  else let
    val stop = find_byte(text, text_len, i, 10)
  in
    if stop >= text_len then i else _line_start(text, text_len, stop + 1, number + 1, target)
  end

(* The refusal, on standard error: the file, the line number and the line *)
fn _say_refused {pl:agz}{pn:pos}{path_len:nat | path_len <= pn}
  {tl:agz}{tn:pos}{text_len:nat | text_len <= tn}
  (path: !$A.borrow(byte, pl, pn), path_len: int path_len,
   text: !$A.borrow(byte, tl, tn), text_len: int text_len, number: int): void = let
  val start = _line_start(text, text_len, 0, 1, number)
  val stop = find_byte(text, text_len, start, 10)
  val () = prerr! ("repin: refused, not a plain uses line of a pin: ")
  val () = _err_range(path, 0, path_len)
  val () = prerr! (":", number, ": ")
  val () = _err_range(text, start, stop)
  val () = prerrln! ()
in () end

(* One file: its text rewritten in memory (records appended to records); a refused line
   leaves the file alone. When write is true a file with a moved pin is written over
   itself. 0 when it went well, else 1 (said on standard error). *)
fn _process_file {pl:agz}{pn:pos}{path_len:nat | path_len <= pn; path_len < 524288}
  {rl:agz}{rn:pos | rn <= 524288}{releases_len:nat | releases_len <= rn}
  (path: !$A.borrow(byte, pl, pn), path_len: int path_len,
   releases: !$A.borrow(byte, rl, rn), releases_len: int releases_len, now: lint, write: bool,
   records: !$B.sized_rope): int = let
  var text : $B.builder(0) = $B.create()
  val @(ended, words) = read_file(path, path_len, text)
  val @(text_array, text_len) = $B.to_arr(text)
  val @(text_frozen, text_view) = $A.freeze<byte>(text_array)
  val status =
    (case+ ended of
     | Read_failed() => let
         val () = prerr! ("repin: cannot read ")
         val () = _err_range(path, 0, path_len)
         val () = prerrln! (": ", words)
       in 1 end
     | Read_too_long() => let
         val () = prerr! ("repin: over 524288 bytes: ")
         val () = _err_range(path, 0, path_len)
         val () = prerrln! ()
       in 1 end
     | Read_whole() => let
         val out = $B.sized_rope_create()
         val @(bad, changed) = rewrite_actions(text_view, text_len, releases, releases_len, now,
             out, records)
       in
         if bad > 0 then let
           val () = _say_refused(path, path_len, text_view, text_len, bad)
           val () = discard_rope(out)
         in 1 end
         else if write && changed then
           (if write_rope_file(path, path_len, out) then 0
            else let
              val () = prerr! ("repin: cannot write ")
              val () = _err_range(path, 0, path_len)
              val () = prerrln! ()
            in 1 end)
         else let val () = discard_rope(out) in 0 end
       end): int
  val () = $A.drop<byte>(text_frozen, text_view)
  val () = $A.free<byte>($A.thaw<byte>(text_frozen))
in status end

(* The entry i of the directory dir[0, dir_len), when its name ends .yml or .yaml: how
   many files did not go well *)
fn _process_entry {n:nat}{i:nat | i < n}{dl:agz}{dn:pos}{dir_len:nat | dir_len <= dn; dir_len <=
    4096}
  {rl:agz}{rn:pos | rn <= 524288}{releases_len:nat | releases_len <= rn}
  (entries: !$F.entries(n), i: int i, dir: !$A.borrow(byte, dl, dn), dir_len: int dir_len,
   releases: !$A.borrow(byte, rl, rn), releases_len: int releases_len, now: lint, write: bool,
   records: !$B.sized_rope): int = let
  val name_buffer = $A.alloc<byte>(1024)
  val name_len = $F.entries_name(entries, i, name_buffer, 1024)
  val @(name_frozen, name_view) = $A.freeze<byte>(name_buffer)
  val workflow =
    (if name_len >= 5 && span_is(name_view, name_len - 5, name_len, ".yaml") then true
     else if name_len >= 4 then span_is(name_view, name_len - 4, name_len, ".yml")
     else false): bool
  val status =
    (if ~workflow then 0
     else let
       var path : $B.builder(0) = $B.create()
       val () = put_range(dir, 0, dir_len, path)
       val () = $B.put_char(path, $AR.low_byte(47))
       val () = put_range(name_view, 0, name_len, path)
       val @(path_array, path_len) = $B.to_arr(path)
       val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
       val status = _process_file(path_view, path_len, releases, releases_len, now, write, records)
       val () = $A.drop<byte>(path_frozen, path_view)
       val () = $A.free<byte>($A.thaw<byte>(path_frozen))
     in status end): int
  val () = $A.drop<byte>(name_frozen, name_view)
  val () = $A.free<byte>($A.thaw<byte>(name_frozen))
in status end

fun _each_entry {n:nat}{i:nat | i <= n}{dl:agz}{dn:pos}{dir_len:nat | dir_len <= dn; dir_len <=
    4096}
  {rl:agz}{rn:pos | rn <= 524288}{releases_len:nat | releases_len <= rn} .<n - i>.
  (entries: !$F.entries(n), n: int n, i: int i, dir: !$A.borrow(byte, dl, dn), dir_len: int dir_len,
   releases: !$A.borrow(byte, rl, rn), releases_len: int releases_len, now: lint, write: bool,
   records: !$B.sized_rope): int =
  if i >= n then 0
  else let
    val failed = _process_entry(entries, i, dir, dir_len, releases, releases_len, now, write,
        records)
  in failed + _each_entry(entries, n, i + 1, dir, dir_len, releases, releases_len, now, write,
      records) end

(* The writing pass, unless the first failed: how many files did not go well *)
fn _write_pass {n:nat}{dl:agz}{dn:pos}{dir_len:nat | dir_len <= dn; dir_len <= 4096}
  {rl:agz}{rn:pos | rn <= 524288}{releases_len:nat | releases_len <= rn}
  (first: int, entries: !$F.entries(n), n: int n, dir: !$A.borrow(byte, dl, dn), dir_len: int
      dir_len,
   releases: !$A.borrow(byte, rl, rn), releases_len: int releases_len, now: lint,
   records: !$B.sized_rope): int =
  if first > 0 then 1
  else _each_entry(entries, n, 0, dir, dir_len, releases, releases_len, now, true, records)

(* Both passes over the entries of the directory: whether every file went well *)
fn _rewrite_directory {dl:agz}{dn:pos}{dir_len:nat | dir_len <= dn; dir_len <= 4096}
  {rl:agz}{rn:pos | rn <= 524288}{releases_len:nat | releases_len <= rn}
  (dir: !$A.borrow(byte, dl, dn), dir_len: int dir_len,
   releases: !$A.borrow(byte, rl, rn), releases_len: int releases_len, now: lint,
   records: !$B.sized_rope): int =
  case+ list_directory(dir, dir_len) of
  | ~$R.err(failure) => let
      val () = prerrln! ("repin: cannot read the workflow directory: ", $F.io_error_text(failure))
    in 1 end
  | ~$R.ok(entries) => let
      val count = $F.entries_count(entries)
      val scratch = $B.sized_rope_create()
      val first = _each_entry(entries, count, 0, dir, dir_len, releases, releases_len, now, false,
          scratch)
      val () = discard_rope(scratch)
      val second = _write_pass(first, entries, count, dir, dir_len, releases, releases_len, now,
          records)
      val () = $F.entries_free(entries)
    in if second > 0 then 1 else 0 end

(* Rewrites the action pins of the workflow files of the directory args[dir_start,
   dir_stop) by the releases file args[releases_start, releases_stop) at the time now (whole
   seconds): 0 when it went well, with the move records appended to records, else 1 (said on
   standard error) with no file written when a file has a refused line or the releases file
   is not release lines. *)
#pub fn run_actions {l:agz}{n:pos}{dir_stop:nat | dir_stop <= n}
  {dir_start:nat | dir_start <= dir_stop; dir_stop - dir_start <= 4096}
  {releases_stop:nat | releases_stop <= n}
  {releases_start:nat | releases_start <= releases_stop; releases_stop - releases_start <= 4096}
  (args: !$A.borrow(byte, l, n), dir_start: int dir_start, dir_stop: int dir_stop,
   releases_start: int releases_start, releases_stop: int releases_stop, now: lint,
   records: !$B.sized_rope): int

implement run_actions (args, dir_start, dir_stop, releases_start, releases_stop, now, records) = let
  var dir_builder : $B.builder(0) = $B.create()
  val () = put_range(args, dir_start, dir_stop, dir_builder)
  val @(dir_array, dir_len) = $B.to_arr(dir_builder)
  val @(dir_frozen, dir_view) = $A.freeze<byte>(dir_array)
  var releases_path : $B.builder(0) = $B.create()
  val () = put_range(args, releases_start, releases_stop, releases_path)
  val @(path_array, path_len) = $B.to_arr(releases_path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var releases_builder : $B.builder(0) = $B.create()
  val @(ended, words) = read_file(path_view, path_len, releases_builder)
  val @(releases_array, releases_len) = $B.to_arr(releases_builder)
  val @(releases_frozen, releases_view) = $A.freeze<byte>(releases_array)
  val status =
    (case+ ended of
     | Read_failed() => let
         val () = prerrln! ("repin: cannot read the releases: ", words)
       in 1 end
     | Read_too_long() => let
         val () = prerrln! ("repin: the releases file is over 524288 bytes")
       in 1 end
     | Read_whole() => let
         val bad = validate_releases(releases_view, releases_len)
       in
         if bad > 0 then let
           val () = prerrln! ("repin: line ", bad, " of the releases is not a release")
         in 1 end
         else _rewrite_directory(dir_view, dir_len, releases_view, releases_len, now, records)
       end): int
  val () = $A.drop<byte>(releases_frozen, releases_view)
  val () = $A.free<byte>($A.thaw<byte>(releases_frozen))
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val () = $A.drop<byte>(dir_frozen, dir_view)
  val () = $A.free<byte>($A.thaw<byte>(dir_frozen))
in status end
