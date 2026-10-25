(* pathrule_driver -- `repin paths-check` and `repin members-check` (bats-lang/repository-
   prototype#466). Keyword: repin path rule.

   The files are read whole (support.bats), so each is at most 524288 bytes. The words of a
   refusal are the message, printed by the caller; a file that cannot be read is said on
   standard error. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "age.sats"
staload "pathrule.sats"
staload "support.sats"

(* The file named by args[start, stop) read into a builder: how the read ended *)
fn _read_named {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop; stop - start <= 4096}
  (args: !$A.borrow(byte, l, n), start: int start, stop: int stop,
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
  | Read_failed() => let val () = prerrln! ("repin: cannot read a file: ", words) in false end
  | Read_too_long() => let val () = prerrln! ("repin: a file is over 524288 bytes") in false end
  | Read_whole() => true
end

(* The paths file at args[paths_start, paths_stop) checked by the rule: 0 when it passes, else
   1 with the refusal in message (1 too when the file cannot be read) *)
#pub fn run_paths_check {args_loc:agz}{args_size:pos}{paths_stop:nat | paths_stop <= args_size}
  {paths_start:nat | paths_start <= paths_stop; paths_stop - paths_start <= 4096}
  (args: !$A.borrow(byte, args_loc, args_size), paths_start: int paths_start,
   paths_stop: int paths_stop, message: !$B.sized_rope): int

implement run_paths_check (args, paths_start, paths_stop, message) = let
  var paths : $B.builder(0) = $B.create()
  val read = _read_named(args, paths_start, paths_stop, paths)
  val @(paths_array, paths_len) = $B.to_arr(paths)
  val @(paths_frozen, paths_view) = $A.freeze<byte>(paths_array)
  val status = (if read then check_paths(paths_view, paths_len, message) else 1): int
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
  cap_start, cap_stop, message) = let
  val @(cap_ok, cap) = parse_seconds(args, cap_start, cap_stop)
in
  if ~cap_ok then let val () = prerrln! ("repin: MAX_BYTES is 1 to 12 digits") in 1 end
  else let
    var listing : $B.builder(0) = $B.create()
    val listing_read = _read_named(args, listing_start, listing_stop, listing)
    val @(listing_array, listing_len) = $B.to_arr(listing)
    val @(listing_frozen, listing_view) = $A.freeze<byte>(listing_array)
    var paths : $B.builder(0) = $B.create()
    val paths_read = _read_named(args, paths_start, paths_stop, paths)
    val @(paths_array, paths_len) = $B.to_arr(paths)
    val @(paths_frozen, paths_view) = $A.freeze<byte>(paths_array)
    val status =
      (if listing_read && paths_read then
         check_members(listing_view, listing_len, paths_view, paths_len, cap, message)
       else 1): int
    val () = $A.drop<byte>(paths_frozen, paths_view)
    val () = $A.free<byte>($A.thaw<byte>(paths_frozen))
    val () = $A.drop<byte>(listing_frozen, listing_view)
    val () = $A.free<byte>($A.thaw<byte>(listing_frozen))
  in status end
end
