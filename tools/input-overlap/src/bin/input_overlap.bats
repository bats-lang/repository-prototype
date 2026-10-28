(* input_overlap -- an action or a reusable workflow keeps an input it removes for one relock cycle
   (bats-lang/repository-prototype#544). Keyword: input-overlap.

     input_overlap check BASEDIR HEADDIR OLDDIR CHANGES

   CHANGES is a file of the paths a pull request changes, one on each line (git diff --name-only
   --no-renames, so a rename is a removal and an addition). BASEDIR is a checkout of the default
   branch's commit the pull request is based on, HEADDIR a checkout of the pull request's head, OLDDIR a
   checkout of the default branch one relock cycle (24 hours) earlier. For each changed path that is
   an action.yml or a workflow, every input BASEDIR declares must still be declared by HEADDIR, unless
   OLDDIR already marked it deprecated: so an input is removed in two steps, a pull request that
   marks it deprecated (and keeps it working) and, a relock cycle after it merged, one that removes it.
   A file that is not in a directory reads as having no inputs. Each refusal is printed as a
   workflow ::error:: command naming the file and the input; the status is 1 when there is one.

   It reads the files it is given, makes no network call, parses no YAML (it reads the
   lines, inputs.bats) and no clock. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use result as R

staload "inputs.sats"
staload "overlap.sats"
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

(* The argument at index (the program's own name is 0): where it starts and ends; absent when it
   starts at args_len *)
fn _argument {l:agz}{n:pos}{args_len:nat | args_len <= n}{index:nat}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, index: int index)
  : [start,stop:nat | start <= stop; stop <= args_len] @(int start, int stop) = let
  val start = _skip_arguments(args, args_len, 0, index)
  val stop = find_byte(args, args_len, start, 0)
in @(start, stop) end

(* The file DIR/PATH read whole (dir from the arguments, path from the changes): the array and its
   length; a file that is not there or cannot be read, or is too long, is an empty text and false *)
fn _load {dl:agz}{dn:pos | dn <= 4096}{dstop:nat | dstop <= dn}{dstart:nat | dstart <= dstop}
  {pl:agz}{pn:pos}{pstop:nat | pstop <= pn}{pstart:nat | pstart <= pstop}
  (args: !$A.borrow(byte, dl, dn), dir_start: int dstart, dir_stop: int dstop,
   changes: !$A.borrow(byte, pl, pn), path_start: int pstart, path_stop: int pstop)
  : @(bool, [m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) =
  if path_stop - path_start > 1000 then let
    var empty : $B.builder(0) = $B.create()
    val @(array, used) = $B.to_arr(empty)
  in @(false, array, 0) end
  else let
    var path : $B.builder(0) = $B.create()
    val () = put_range(args, dir_start, dir_stop, path)
    val () = $B.put_char(path, 47)
    val () = put_range(changes, path_start, path_stop, path)
    val @(path_array, path_len) = $B.to_arr(path)
    val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
    var text : $B.builder(0) = $B.create()
    val @(ended, _) = read_file(path_view, path_len, text)
    val () = $A.drop<byte>(path_frozen, path_view)
    val () = $A.free<byte>($A.thaw<byte>(path_frozen))
    val @(array, used) = $B.to_arr(text)
  in
    case+ ended of
    | Read_whole() => @(true, array, used)
    | _ => @(false, array, 0)
  end

(* One changed path: how many inputs it removes wrongly *)
fn _check_path {dl:agz}{dn:pos | dn <= 4096}{args_len:nat | args_len <= dn}
  {bs,be,hs,he,os,oe:nat | bs <= be; be <= dn; hs <= he; he <= dn; os <= oe; oe <= dn}
  {pl:agz}{pn:pos}{pstop:nat | pstop <= pn}{pstart:nat | pstart <= pstop}
  (args: !$A.borrow(byte, dl, dn), args_len: int args_len,
   base_start: int bs, base_stop: int be, head_start: int hs, head_stop: int he, old_start: int os, old_stop: int oe,
   changes: !$A.borrow(byte, pl, pn), path_start: int pstart, path_stop: int pstop): int =
  (case+ file_kind_of(changes, path_start, path_stop) of
   | Not_interface() => 0
   | kind =>
     let
       val @(base_ok, base_array, base_len) =
         _load(args, base_start, base_stop, changes, path_start, path_stop)
       val @(head_ok, head_array, head_len) =
         _load(args, head_start, head_stop, changes, path_start, path_stop)
       val @(old_ok, old_array, old_len) =
         _load(args, old_start, old_stop, changes, path_start, path_stop)
       val @(base_frozen, base_view) = $A.freeze<byte>(base_array)
       val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
       val @(old_frozen, old_view) = $A.freeze<byte>(old_array)
       val count = removed_inputs(base_view, base_len, head_view, head_len, old_view, old_len, kind,
         changes, path_start, path_stop)
       val () = $A.drop<byte>(base_frozen, base_view)
       val () = $A.free<byte>($A.thaw<byte>(base_frozen))
       val () = $A.drop<byte>(head_frozen, head_view)
       val () = $A.free<byte>($A.thaw<byte>(head_frozen))
       val () = $A.drop<byte>(old_frozen, old_view)
       val () = $A.free<byte>($A.thaw<byte>(old_frozen))
     in count end)

fun _each_path {dl:agz}{dn:pos | dn <= 4096}{args_len:nat | args_len <= dn}
  {bs,be,hs,he,os,oe:nat | bs <= be; be <= dn; hs <= he; he <= dn; os <= oe; oe <= dn}
  {pl:agz}{pn:pos}{plen:nat | plen <= pn}{at:nat | at <= plen} .<plen - at>.
  (args: !$A.borrow(byte, dl, dn), args_len: int args_len,
   base_start: int bs, base_stop: int be, head_start: int hs, head_stop: int he, old_start: int os, old_stop: int oe,
   changes: !$A.borrow(byte, pl, pn), plen: int plen, at: int at): int =
  if at >= plen then 0
  else let
    val line_stop = find_byte(changes, plen, at, 10)
    val here = (if line_stop > at then
                  _check_path(args, args_len, base_start, base_stop, head_start, head_stop,
                    old_start, old_stop, changes, at, line_stop)
                else 0): int
  in
    if line_stop >= plen then here
    else here + _each_path(args, args_len, base_start, base_stop, head_start, head_stop,
                   old_start, old_stop, changes, plen, line_stop + 1)
  end

fn _check {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): int = let
  val @(base_start, base_stop) = _argument(args, args_len, 2)
  val @(head_start, head_stop) = _argument(args, args_len, 3)
  val @(old_start, old_stop) = _argument(args, args_len, 4)
  val @(changes_start, changes_stop) = _argument(args, args_len, 5)
  val @(extra_start, _) = _argument(args, args_len, 6)
in
  if changes_start >= args_len || extra_start < args_len then let
    val () = prerrln! ("usage: input_overlap check BASEDIR HEADDIR OLDDIR CHANGES")
  in 2 end
  else let
    var changes_path : $B.builder(0) = $B.create()
    val () = put_range(args, changes_start, changes_stop, changes_path)
    val @(path_array, path_len) = $B.to_arr(changes_path)
    val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
    var text : $B.builder(0) = $B.create()
    val @(ended, words) = read_file(path_view, path_len, text)
    val () = $A.drop<byte>(path_frozen, path_view)
    val () = $A.free<byte>($A.thaw<byte>(path_frozen))
    val @(array, used) = $B.to_arr(text)
    val @(frozen, view) = $A.freeze<byte>(array)
    val status =
      (case+ ended of
       | Read_whole() => let
           val removed = _each_path(args, args_len, base_start, base_stop, head_start, head_stop,
             old_start, old_stop, view, used, 0)
         in if removed = 0 then 0 else 1 end
       | Read_too_long() => let
           val () = prerrln! ("input-overlap: the changes file is longer than the check reads")
         in 1 end
       | Read_failed() => let
           val () = prerrln! ("input-overlap: cannot read the changes file: ", words)
         in 1 end): int
    val () = $A.drop<byte>(frozen, view)
    val () = $A.free<byte>($A.thaw<byte>(frozen))
  in status end
end

fn _usage (): int = let
  val () = prerrln! ("usage: input_overlap check BASEDIR HEADDIR OLDDIR CHANGES")
in 2 end

implement main0 () = let
  val buffer = $A.alloc<byte>(4096)
  val length =
    (case+ $E.args_read(buffer, 4096) of
     | ~$R.some(count) => count
     | ~$R.none() => 0): [count:nat | count <= 4096] int count
  val @(frozen, view) = $A.freeze<byte>(buffer)
  val @(command_start, command_stop) = _argument(view, length, 1)
  val status =
    (if command_start >= length then _usage()
     else if span_is(view, command_start, command_stop, "check") then _check(view, length)
     else _usage()): int
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in
  if status = 0 then () else exit_void(status)
end
