(* gradle_driver -- `repin gradle` over files (bats-lang/repository-prototype#413).
   Keyword: repin gradle.

   The properties, versions and checksum files are read whole (each at most 524288 bytes, the
   bound of a text of repin); the decision is made in memory (gradle.bats), and only when it
   went well are the move records handed to the caller and the update lines written to its
   file: the version and the checksum of the target when the pin moves, else an empty file. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "gradle.sats"
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

(* The files read, the decision made and the update lines written; 0 when it went well,
   with the move records appended to records, else 1 (said on standard error) and nothing
   written *)
fn _decide_files {l:agz}{n:pos}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop; updates_stop - updates_start <= 4096}
  {checksum_stop:nat | checksum_stop <= n}{checksum_start:nat | checksum_start <= checksum_stop; checksum_stop - checksum_start <= 4096}
  {versions_stop:nat | versions_stop <= n}{versions_start:nat | versions_start <= versions_stop; versions_stop - versions_start <= 4096}
  {properties_stop:nat | properties_stop <= n}{properties_start:nat | properties_start <= properties_stop; properties_stop - properties_start <= 4096}
  (args: !$A.borrow(byte, l, n), properties_start: int properties_start,
   properties_stop: int properties_stop, versions_start: int versions_start,
   versions_stop: int versions_stop, checksum_start: int checksum_start,
   checksum_stop: int checksum_stop, updates_start: int updates_start,
   updates_stop: int updates_stop, now: lint, records: !$B.sized_rope): int = let
  var properties_builder : $B.builder(0) = $B.create()
  val properties_read = _read_argument(args, properties_start, properties_stop, "properties",
    properties_builder)
  val @(properties_array, properties_len) = $B.to_arr(properties_builder)
  val @(properties_frozen, properties_view) = $A.freeze<byte>(properties_array)
  var versions_builder : $B.builder(0) = $B.create()
  val versions_read = _read_argument(args, versions_start, versions_stop, "versions",
    versions_builder)
  val @(versions_array, versions_len) = $B.to_arr(versions_builder)
  val @(versions_frozen, versions_view) = $A.freeze<byte>(versions_array)
  var checksum_builder : $B.builder(0) = $B.create()
  val checksum_read = _read_argument(args, checksum_start, checksum_stop, "checksum",
    checksum_builder)
  val @(checksum_array, checksum_len) = $B.to_arr(checksum_builder)
  val @(checksum_frozen, checksum_view) = $A.freeze<byte>(checksum_array)
  val updates = $B.sized_rope_create()
  val status =
    (if properties_read && versions_read && checksum_read then
       decide_gradle(properties_view, properties_len, versions_view, versions_len,
         checksum_view, checksum_len, now, records, updates)
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
  val () = $A.drop<byte>(checksum_frozen, checksum_view)
  val () = $A.free<byte>($A.thaw<byte>(checksum_frozen))
  val () = $A.drop<byte>(versions_frozen, versions_view)
  val () = $A.free<byte>($A.thaw<byte>(versions_frozen))
  val () = $A.drop<byte>(properties_frozen, properties_view)
  val () = $A.free<byte>($A.thaw<byte>(properties_frozen))
in
  if status <> 0 then 1
  else if written then 0
  else let val () = prerrln! ("repin: cannot write the update lines") in 1 end
end

(* The properties file at args[properties_start, properties_stop), the versions file, the
   checksum file and the update file (written) decide the move at now (whole seconds); the
   move records are appended to records. 0 when it went well, else 1 (said on standard
   error). *)
#pub fn run_gradle {l:agz}{n:pos}
  {updates_stop:nat | updates_stop <= n}{updates_start:nat | updates_start <= updates_stop; updates_stop - updates_start <= 4096}
  {checksum_stop:nat | checksum_stop <= n}{checksum_start:nat | checksum_start <= checksum_stop; checksum_stop - checksum_start <= 4096}
  {versions_stop:nat | versions_stop <= n}{versions_start:nat | versions_start <= versions_stop; versions_stop - versions_start <= 4096}
  {properties_stop:nat | properties_stop <= n}{properties_start:nat | properties_start <= properties_stop; properties_stop - properties_start <= 4096}
  (args: !$A.borrow(byte, l, n), properties_start: int properties_start,
   properties_stop: int properties_stop, versions_start: int versions_start,
   versions_stop: int versions_stop, checksum_start: int checksum_start,
   checksum_stop: int checksum_stop, updates_start: int updates_start,
   updates_stop: int updates_stop, now: lint, records: !$B.sized_rope): int

implement run_gradle (args, properties_start, properties_stop, versions_start, versions_stop,
  checksum_start, checksum_stop, updates_start, updates_stop, now, records) =
  _decide_files(args, properties_start, properties_stop, versions_start, versions_stop,
    checksum_start, checksum_stop, updates_start, updates_stop, now, records)
