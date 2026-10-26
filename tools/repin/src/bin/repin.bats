(* repin -- the relock's pin mover (bats-lang/repository-prototype#410).
   Keyword: repin.

     repin table RECORDS      the Markdown table of the move records in the
                              file RECORDS (the relock pull request's body)
     repin age NOW PUBLISHED  whether a release published at PUBLISHED (whole
                              seconds since the epoch) is a candidate at NOW
     repin actions DIR NOW RELEASES
                              the action pins of the workflow files of DIR
                              moved by the releases file RELEASES at NOW
                              (actions.bats, driver.bats); the move records
                              are printed
     repin npm OUTDATED COMPATIBLE TIMES NOW UPDATES
                              the npm dependencies of `pnpm outdated --format json`
                              (OUTDATED) and its `--compatible` form (COMPATIBLE) moved
                              by the registry's publish times (TIMES) at NOW (npm.bats):
                              the move records are printed and the lines name@version of
                              the moves are written to the file UPDATES
     repin gradle PROPERTIES VERSIONS CHECKSUM NOW UPDATES
                              the gradle-wrapper.properties PROPERTIES moved by the
                              body of Gradle's versions/all (VERSIONS) and the published
                              checksum of the target (CHECKSUM) at NOW (gradle.bats): the
                              move records are printed and, for a move, the version and
                              the checksum are written to the file UPDATES, a line each
     repin paths-check PATHS  the repin path rule (#420, #466; pathrule.bats) on the lines of
                              the file PATHS: at least one path, none refused; a refusal is
                              printed as a workflow `::error::` command
     repin members-check LISTING PATHS MAX_BYTES
                              the listing LISTING (`tar -tv --numeric-owner
                              --quoting-style=escape`) of a tar against PATHS: each member a
                              regular file or directory passing the rule, a listed path or
                              under one, the sizes at most MAX_BYTES, every path a member

   Exit status: 0 done, 1 a file that cannot be read or is not records, 2 the
   command line is not one of these. It reads the files it is given, makes no
   network call, reads no YAML and reads no clock: NOW is an argument. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use result as R

staload "age.sats"
staload "driver.sats"
staload "gradle_driver.sats"
staload "npm_driver.sats"
staload "pathrule_driver.sats"
staload "records.sats"
staload "support.sats"

fun _skip_arguments {l:agz}{n:pos}{args_len:nat | args_len <= n}
  {i:nat | i <= args_len}{count:nat} .<count>.
  (args: !$A.borrow(byte, l, n), args_len: int args_len, i: int i, count: int count)
  : [j:nat | i <= j; j <= args_len] int j =
  if count <= 0 then i
  else let
    val stop = find_byte(args, args_len, i, 0)
  in
    if stop >= args_len then args_len
    else _skip_arguments(args, args_len, stop + 1, count - 1)
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

(* The directory of workflows at args[dir_start, dir_stop) repinned by the releases file
   at args[releases_start, releases_stop) at the time args[now_start, now_stop) (whole
   seconds): the move records on standard output; 1 when it failed (nothing written) *)
fn _actions {l:agz}{n:pos | n <= 4096}
  {dir_stop:nat | dir_stop <= n}{dir_start:nat | dir_start <= dir_stop}
  {now_stop:nat | now_stop <= n}{now_start:nat | now_start <= now_stop}
  {releases_stop:nat | releases_stop <= n}{releases_start:nat | releases_start <= releases_stop}
  (args: !$A.borrow(byte, l, n), dir_start: int dir_start, dir_stop: int dir_stop,
   now_start: int now_start, now_stop: int now_stop,
   releases_start: int releases_start, releases_stop: int releases_stop)
  : int = let
  val @(now_ok, now) = parse_seconds(args, now_start, now_stop)
in
  if now_ok then let
    val records = $B.sized_rope_create()
    val status =
      run_actions(args, dir_start, dir_stop, releases_start, releases_stop, now, records)
    val () = if status = 0 then print_rope(records) else discard_rope(records)
  in status end
  else let val () = prerrln! ("repin: NOW is 1 to 12 digits") in 1 end
end

(* The npm dependencies of the outdated file at args[outdated_start, outdated_stop) and the
   compatible and times files, at the time args[now_start, now_stop) (whole seconds): the
   move records on standard output and the update lines in the file at args[updates_start,
   updates_stop); 1 when it failed (nothing written) *)
fn _npm {l:agz}{n:pos | n <= 4096}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop}
  {now_stop:nat | now_stop <= n}{now_start:nat | now_start <= now_stop}
  {times_stop:nat | times_stop <= n}{times_start:nat | times_start <= times_stop}
  {compat_stop:nat | compat_stop <= n}{compat_start:nat | compat_start <= compat_stop}
  {outdated_stop:nat | outdated_stop <= n}{outdated_start:nat | outdated_start <= outdated_stop}
  (args: !$A.borrow(byte, l, n), outdated_start: int outdated_start,
   outdated_stop: int outdated_stop, compat_start: int compat_start,
   compat_stop: int compat_stop, times_start: int times_start, times_stop: int times_stop,
   now_start: int now_start, now_stop: int now_stop, updates_start: int updates_start,
   updates_stop: int updates_stop): int = let
  val @(now_ok, now) = parse_seconds(args, now_start, now_stop)
in
  if now_ok then let
    val records = $B.sized_rope_create()
    val status = run_npm(args, outdated_start, outdated_stop, compat_start, compat_stop,
      times_start, times_stop, updates_start, updates_stop, now, records)
    val () = if status = 0 then print_rope(records) else discard_rope(records)
  in status end
  else let val () = prerrln! ("repin: NOW is 1 to 12 digits") in 1 end
end

(* The wrapper properties file at args[properties_start, properties_stop), the versions and
   checksum files, at the time args[now_start, now_stop) (whole seconds): the move records
   on standard output and the version and checksum lines in the file at args[updates_start,
   updates_stop); 1 when it failed (nothing written) *)
fn _gradle {l:agz}{n:pos | n <= 4096}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop}
  {now_stop:nat | now_stop <= n}{now_start:nat | now_start <= now_stop}
  {checksum_stop:nat | checksum_stop <= n}{checksum_start:nat | checksum_start <= checksum_stop}
  {versions_stop:nat | versions_stop <= n}{versions_start:nat | versions_start <= versions_stop}
  {properties_stop:nat | properties_stop <= n}{properties_start:nat | properties_start <= properties_stop}
  (args: !$A.borrow(byte, l, n), properties_start: int properties_start,
   properties_stop: int properties_stop, versions_start: int versions_start,
   versions_stop: int versions_stop, checksum_start: int checksum_start,
   checksum_stop: int checksum_stop, now_start: int now_start, now_stop: int now_stop,
   updates_start: int updates_start, updates_stop: int updates_stop): int = let
  val @(now_ok, now) = parse_seconds(args, now_start, now_stop)
in
  if now_ok then let
    val records = $B.sized_rope_create()
    val status = run_gradle(args, properties_start, properties_stop, versions_start,
      versions_stop, checksum_start, checksum_stop, updates_start, updates_stop, now, records)
    val () = if status = 0 then print_rope(records) else discard_rope(records)
  in status end
  else let val () = prerrln! ("repin: NOW is 1 to 12 digits") in 1 end
end

(* The paths file at args[paths_start, paths_stop) checked by the repin path rule; the refusal
   is printed on standard output (a workflow command) *)
fn _paths_check {l:agz}{n:pos | n <= 4096}{paths_stop:nat | paths_stop <= n}
  {paths_start:nat | paths_start <= paths_stop}
  (args: !$A.borrow(byte, l, n), paths_start: int paths_start, paths_stop: int paths_stop): int = let
  val message = $B.sized_rope_create()
  val status = run_paths_check(args, paths_start, paths_stop, message)
  val () = print_rope(message)
in status end

(* The tar listing at args[listing_start, listing_stop) checked against the paths file and the
   cap on the sizes *)
fn _members_check {l:agz}{n:pos | n <= 4096}
  {cap_stop:nat | cap_stop <= n}{cap_start:nat | cap_start <= cap_stop}
  {paths_stop:nat | paths_stop <= n}{paths_start:nat | paths_start <= paths_stop}
  {listing_stop:nat | listing_stop <= n}{listing_start:nat | listing_start <= listing_stop}
  (args: !$A.borrow(byte, l, n), listing_start: int listing_start,
   listing_stop: int listing_stop, paths_start: int paths_start, paths_stop: int paths_stop,
   cap_start: int cap_start, cap_stop: int cap_stop): int = let
  val message = $B.sized_rope_create()
  val status = run_members_check(args, listing_start, listing_stop, paths_start, paths_stop,
    cap_start, cap_stop, message)
  val () = print_rope(message)
in status end

fn _usage (): int = let
  val () = prerrln! ("usage: repin table RECORDS | repin age NOW PUBLISHED")
  val () = prerrln! ("       repin actions DIR NOW RELEASES")
  val () = prerrln! ("       repin npm OUTDATED COMPATIBLE TIMES NOW UPDATES")
  val () = prerrln! ("       repin gradle PROPERTIES VERSIONS CHECKSUM NOW UPDATES")
  val () = prerrln! ("       repin paths-check PATHS | repin members-check LISTING PATHS MAX_BYTES")
in 2 end

(* The argument at index (the program is 0) of the NUL-separated arguments
   args[0, args_len): where it starts and where it ends; it is absent when it
   starts at args_len *)
fn _argument {l:agz}{n:pos}{args_len:nat | args_len <= n}{index:nat}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, index: int index)
  : [start,stop:nat | start <= stop; stop <= args_len] @(int start, int stop) = let
  val start = _skip_arguments(args, args_len, 0, index)
  val stop = find_byte(args, args_len, start, 0)
in @(start, stop) end

fn _command {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): int = let
  val @(command_start, command_stop) = _argument(args, args_len, 1)
  val @(second_start, second_stop) = _argument(args, args_len, 2)
  val @(third_start, third_stop) = _argument(args, args_len, 3)
  val @(fourth_start, fourth_stop) = _argument(args, args_len, 4)
  val @(fifth_start, fifth_stop) = _argument(args, args_len, 5)
  val @(sixth_start, sixth_stop) = _argument(args, args_len, 6)
  val @(seventh_start, _) = _argument(args, args_len, 7)
in
  if command_start >= args_len then _usage()
  else if span_is(args, command_start, command_stop, "table") then
    (if second_start < args_len && third_start >= args_len
     then _table(args, second_start, second_stop) else _usage())
  else if span_is(args, command_start, command_stop, "age") then
    (if third_start < args_len && fourth_start >= args_len
     then _age(args, second_start, second_stop, third_start, third_stop) else _usage())
  else if span_is(args, command_start, command_stop, "actions") then
    (if fourth_start < args_len && fifth_start >= args_len
     then _actions(args, second_start, second_stop, third_start, third_stop,
       fourth_start, fourth_stop)
     else _usage())
  else if span_is(args, command_start, command_stop, "npm") then
    (if sixth_start < args_len && seventh_start >= args_len
     then _npm(args, second_start, second_stop, third_start, third_stop, fourth_start,
       fourth_stop, fifth_start, fifth_stop, sixth_start, sixth_stop)
     else _usage())
  else if span_is(args, command_start, command_stop, "gradle") then
    (if sixth_start < args_len && seventh_start >= args_len
     then _gradle(args, second_start, second_stop, third_start, third_stop, fourth_start,
       fourth_stop, fifth_start, fifth_stop, sixth_start, sixth_stop)
     else _usage())
  else if span_is(args, command_start, command_stop, "paths-check") then
    (if second_start < args_len && third_start >= args_len
     then _paths_check(args, second_start, second_stop) else _usage())
  else if span_is(args, command_start, command_stop, "members-check") then
    (if fourth_start < args_len && fifth_start >= args_len
     then _members_check(args, second_start, second_stop, third_start, third_stop,
       fourth_start, fourth_stop)
     else _usage())
  else _usage()
end

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val length =
    (case+ $E.args_read(buffer, 4096) of
     | ~$R.some(count) => count
     | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(frozen, view) = $A.freeze<byte>(buffer)
  val status = _command(view, length)
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if status = 0 then () else exit_void(status)
end
