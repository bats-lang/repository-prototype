(* npm_driver -- `repin npm` over files (bats-lang/repository-prototype#412).
   Keyword: repin npm.

   The outdated, compatible and times files are read whole (each at most 524288 bytes, the
   bound of a text of repin); the decision is made in memory (npm.bats), and only when it
   went well are the move records handed to the caller and the update list written to its
   file. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "npm.sats"
staload "support.sats"

(* The file at the path args[start, stop) read whole into the empty builder: how the read
   ended and the words of its error. A failure is said on standard error. *)
fn _read_argument {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop; stop - start <= 4096}
  (args: !$A.borrow(byte, l, n), start: int start, stop: int stop, what: string,
   out: !$B.builder(0) >> $B.builder_v): bool = let
  var path : $B.builder(0) = $B.create()
  val () = put_range(args, start, stop, path)
  val @(path_array, path_len) = $B.to_arr(path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val @(ended, words) = read_file(path_view, path_len, out)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in
  case+ ended of
  | Read_whole() => true
  | Read_failed() => let
      val () = prerrln! ("repin: cannot read the ", what, " file: ", words)
    in false end
  | Read_too_long() => let
      val () = prerrln! ("repin: the ", what, " file is over 524288 bytes")
    in false end
end

(* The files read, the decision made and the update list written; 0 when it went well, with
   the move records appended to records, else 1 (said on standard error) and nothing
   written *)
fn _decide_files {l:agz}{n:pos}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop; updates_stop - updates_start <= 4096}
  {times_stop:nat | times_stop <= n}{times_start:nat | times_start <= times_stop; times_stop - times_start <= 4096}
  {compat_stop:nat | compat_stop <= n}{compat_start:nat | compat_start <= compat_stop; compat_stop - compat_start <= 4096}
  {outdated_stop:nat | outdated_stop <= n}{outdated_start:nat | outdated_start <= outdated_stop; outdated_stop - outdated_start <= 4096}
  (args: !$A.borrow(byte, l, n), outdated_start: int outdated_start,
   outdated_stop: int outdated_stop, compat_start: int compat_start,
   compat_stop: int compat_stop, times_start: int times_start, times_stop: int times_stop,
   updates_start: int updates_start, updates_stop: int updates_stop, now: lint,
   records: !$B.sized_rope): int = let
  var outdated_builder : $B.builder(0) = $B.create()
  val outdated_read = _read_argument(args, outdated_start, outdated_stop, "outdated",
    outdated_builder)
  val @(outdated_array, outdated_len) = $B.to_arr(outdated_builder)
  val @(outdated_frozen, outdated_view) = $A.freeze<byte>(outdated_array)
  var compat_builder : $B.builder(0) = $B.create()
  val compat_read = _read_argument(args, compat_start, compat_stop, "compatible", compat_builder)
  val @(compat_array, compat_len) = $B.to_arr(compat_builder)
  val @(compat_frozen, compat_view) = $A.freeze<byte>(compat_array)
  var times_builder : $B.builder(0) = $B.create()
  val times_read = _read_argument(args, times_start, times_stop, "times", times_builder)
  val @(times_array, times_len) = $B.to_arr(times_builder)
  val @(times_frozen, times_view) = $A.freeze<byte>(times_array)
  val updates = $B.sized_rope_create()
  val status =
    (if outdated_read && compat_read && times_read then
       run_npm_texts(outdated_view, outdated_len, compat_view, compat_len, times_view,
         times_len, now, records, updates)
     else 1): int
  val written =
    (if status = 0 then let
       var path : $B.builder(0) = $B.create()
       val () = put_range(args, updates_start, updates_stop, path)
       val @(path_array, path_len) = $B.to_arr(path)
       val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
       val ok = write_rope_new_file(path_view, path_len, updates)
       val () = $A.drop<byte>(path_frozen, path_view)
       val () = $A.free<byte>($A.thaw<byte>(path_frozen))
     in ok end
     else let val () = discard_rope(updates) in true end): bool
  val () = $A.drop<byte>(times_frozen, times_view)
  val () = $A.free<byte>($A.thaw<byte>(times_frozen))
  val () = $A.drop<byte>(compat_frozen, compat_view)
  val () = $A.free<byte>($A.thaw<byte>(compat_frozen))
  val () = $A.drop<byte>(outdated_frozen, outdated_view)
  val () = $A.free<byte>($A.thaw<byte>(outdated_frozen))
in
  if status <> 0 then 1
  else if written then 0
  else let val () = prerrln! ("repin: cannot write the update list") in 1 end
end

(* The outdated file at args[outdated_start, outdated_stop), the compatible file, the times
   file and the update list file (written) decide the moves at now (whole seconds); the move
   records are appended to records. 0 when it went well, else 1 (said on standard error). *)
#pub fn run_npm {l:agz}{n:pos}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop; updates_stop - updates_start <= 4096}
  {times_stop:nat | times_stop <= n}{times_start:nat | times_start <= times_stop; times_stop - times_start <= 4096}
  {compat_stop:nat | compat_stop <= n}{compat_start:nat | compat_start <= compat_stop; compat_stop - compat_start <= 4096}
  {outdated_stop:nat | outdated_stop <= n}{outdated_start:nat | outdated_start <= outdated_stop; outdated_stop - outdated_start <= 4096}
  (args: !$A.borrow(byte, l, n), outdated_start: int outdated_start,
   outdated_stop: int outdated_stop, compat_start: int compat_start,
   compat_stop: int compat_stop, times_start: int times_start, times_stop: int times_stop,
   updates_start: int updates_start, updates_stop: int updates_stop, now: lint,
   records: !$B.sized_rope): int

implement run_npm (args, outdated_start, outdated_stop, compat_start, compat_stop,
  times_start, times_stop, updates_start, updates_stop, now, records) =
  _decide_files(args, outdated_start, outdated_stop, compat_start, compat_stop, times_start,
    times_stop, updates_start, updates_stop, now, records)
