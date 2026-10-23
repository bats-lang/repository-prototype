(* bats_stand_in -- the `bats` of the verify-archives tests (bats-lang/
   repository-prototype#396; keyword: verify-archives tests).

   scripts/verify-archives.sh runs `bats lock --repository DIR` and
   `bats check --repository DIR` in the unpacked archive of a package. This
   stand-in answers `lock` with success. `check` fails (status 1, a line with
   "error" on standard output) when the current directory holds a file named
   `depends` (the package depends on the repository) and DIR holds a file
   named `BROKEN` (the repository as the change leaves it breaks its
   dependents); otherwise it succeeds. So a test makes an archive pass at the
   base of a change and fail at its head by adding a `BROKEN` file. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use result as R

staload "support.sats"

(* The arguments are NUL-terminated strings back to back in view[0, k): the
   directory after `--repository` from i, as its start and end; found is
   false when there is none *)
fun _repository {l:agz}{k:nat | k <= 8192}{i:nat | i <= k} .<k - i>.
  (view: !$A.borrow(byte, l, 8192), k: int k, i: int i): [found_start,found_stop:nat | found_start <= found_stop; found_stop <= k] @(bool, int found_start, int found_stop) = let
  val stop = find_byte(view, k, i, 0)
in
  if line_is(view, i, stop, "--repository") then
    (if stop >= k then @(false, 0, 0)
     else let val dir_stop = find_byte(view, k, stop + 1, 0) in @(true, stop + 1, dir_stop) end)
  else if stop >= k then @(false, 0, 0)
  else _repository(view, k, stop + 1)
end

(* Whether the file BROKEN is in the directory view[dir_start, dir_stop) *)
fn _broken {l:agz}{dir_start,dir_stop:nat | dir_start <= dir_stop; dir_stop <= 8192}
  (view: !$A.borrow(byte, l, 8192), dir_start: int dir_start, dir_stop: int dir_stop): bool = let
  var path_builder : $B.builder(0) = $B.create()
  val () = put_range(view, dir_start, dir_stop, path_builder)
  val () = $B.bput(path_builder, "/BROKEN")
  val @(path_array, path_len) = $B.to_arr(path_builder)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val present = file_exists(path_view, path_len)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in present end

implement main0 () = let
  val args = $A.alloc<byte>(8192)
  val args_len = (case+ $E.args_read(args, 8192) of | ~$R.some(k) => k | ~$R.none() => 0): [k:nat | k <= 8192] int k
  val @(frozen, view) = $A.freeze<byte>(args)
  val program_end = find_byte(view, args_len, 0, 0)
  val () =
    if program_end >= args_len then ()
    else let
      val command_end = find_byte(view, args_len, program_end + 1, 0)
    in
      if ~line_is(view, program_end + 1, command_end, "check") then ()
      else if command_end >= args_len then ()
      else let
        val @(found, dir_start, dir_stop) = _repository(view, args_len, command_end + 1)
      in
        if ~found then ()
        else if ~_broken(view, dir_start, dir_stop) then ()
        else if ~constant_exists("depends") then ()
        else let
          val () = print! ("error: ")
          val () = print_range(view, dir_start, dir_stop)
          val () = println! ("/BROKEN exists and this package depends on the repository")
        in exit_void(1) end
      end
    end
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in end
