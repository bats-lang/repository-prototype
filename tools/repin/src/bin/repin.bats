(* repin -- the relock's pin mover (bats-lang/repository-prototype#410).
   Keyword: repin.

     repin table RECORDS      the Markdown table of the move records in the
                              file RECORDS (the relock pull request's body)
     repin age NOW PUBLISHED  whether a release published at PUBLISHED (whole
                              seconds since the epoch) is a candidate at NOW

   Exit status: 0 done, 1 a file that cannot be read or is not records, 2 the
   command line is not one of these. It reads the files it is given, makes no
   network call, reads no YAML and reads no clock: NOW is an argument. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use result as R

staload "age.sats"
staload "records.sats"
staload "support.sats"

fun _skip_arguments {l:agz}{n:pos}{k:nat | k <= n}{i:nat | i <= k}{count:nat} .<count>.
  (b: !$A.borrow(byte, l, n), k: int k, i: int i, count: int count)
  : [j:nat | i <= j; j <= k] int j =
  if count <= 0 then i
  else let
    val stop = find_byte(b, k, i, 0)
  in
    if stop >= k then k else _skip_arguments(b, k, stop + 1, count - 1)
  end

(* The records file at the path args[start, stop): the table, or the number
   of its first bad line *)
fn _table {l:agz}{n:pos | n <= 4096}{stop:nat | stop <= n}{start:nat | start <= stop}
  (args: !$A.borrow(byte, l, n), start: int start, stop: int stop): int = let
  var path : $B.builder(0) = $B.create()
  val () = put_range(args, start, stop, path)
  val @(path_array, path_len) = $B.to_arr(path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var records : $B.builder(0) = $B.create()
  val @(ended, words) = read_file(path_view, path_len, records)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val @(records_array, records_len) = $B.to_arr(records)
  val @(records_frozen, records_view) = $A.freeze<byte>(records_array)
  val table = $B.sized_rope_create()
  val status =
    (case+ ended of
     | Read_failed() => let val () = prerrln! ("repin: cannot read the records: ", words) in 1 end
     | Read_too_long() => let
         val () = prerrln! ("repin: the records file is over 524288 bytes")
       in 1 end
     | Read_whole() => let
         val bad = render_table(records_view, records_len, table)
       in
         if bad = 0 then 0
         else let
           val () = prerrln! ("repin: line ", bad, " of the records is not a record")
         in 1 end
       end): int
  val () = $A.drop<byte>(records_frozen, records_view)
  val () = $A.free<byte>($A.thaw<byte>(records_frozen))
  val () = if status = 0 then print_rope(table) else discard_rope(table)
in status end

(* The age of the release published at args[published_start, published_stop)
   at the time args[now_start, now_stop), as a line of words; 1 when either is
   not 1 to 12 digits *)
fn _age {l:agz}{n:pos}{now_stop:nat | now_stop <= n}{now_start:nat | now_start <= now_stop}
  {published_stop:nat | published_stop <= n}
  {published_start:nat | published_start <= published_stop}
  (args: !$A.borrow(byte, l, n), now_start: int now_start, now_stop: int now_stop,
   published_start: int published_start, published_stop: int published_stop): int = let
  val @(now_ok, now) = parse_seconds(args, now_start, now_stop)
  val @(published_ok, published) = parse_seconds(args, published_start, published_stop)
in
  if now_ok && published_ok then let
    val line = $B.sized_rope_create()
    val () = put_days(line, age_days(now, published))
    val () = if is_candidate(now, published) then $B.sized_rope_bput(line, ", candidate\n")
             else $B.sized_rope_bput(line, ", too new\n")
    val () = print_rope(line)
  in 0 end
  else let val () = prerrln! ("repin: NOW and PUBLISHED are each 1 to 12 digits") in 1 end
end

fn _usage (): int = let
  val () = prerrln! ("usage: repin table RECORDS | repin age NOW PUBLISHED")
in 2 end

(* The argument at index (the program is 0) of the NUL-separated arguments
   args[0, k): where it starts and where it ends; it is absent when it starts
   at k *)
fn _argument {l:agz}{n:pos}{k:nat | k <= n}{index:nat}
  (args: !$A.borrow(byte, l, n), k: int k, index: int index)
  : [start,stop:nat | start <= stop; stop <= k] @(int start, int stop) = let
  val start = _skip_arguments(args, k, 0, index)
  val stop = find_byte(args, k, start, 0)
in @(start, stop) end

fn _command {l:agz}{n:pos | n <= 4096}{k:nat | k <= n}
  (args: !$A.borrow(byte, l, n), k: int k): int = let
  val @(command_start, command_stop) = _argument(args, k, 1)
  val @(second_start, second_stop) = _argument(args, k, 2)
  val @(third_start, third_stop) = _argument(args, k, 3)
  val @(fourth_start, fourth_stop) = _argument(args, k, 4)
in
  if command_start >= k then _usage()
  else if span_is(args, command_start, command_stop, "table") then
    (if second_start < k && third_start >= k
     then _table(args, second_start, second_stop) else _usage())
  else if span_is(args, command_start, command_stop, "age") then
    (if third_start < k && fourth_start >= k
     then _age(args, second_start, second_stop, third_start, third_stop) else _usage())
  else _usage()
end

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val length =
    (case+ $E.args_read(buffer, 4096) of
     | ~$R.some(k) => k
     | ~$R.none() => 0): [k:nat | k <= 4096] int k
  val @(frozen, view) = $A.freeze<byte>(buffer)
  val status = _command(view, length)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if status = 0 then () else exit_void(status)
end
