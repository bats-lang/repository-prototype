(* text_lint -- the shared lint of a pull request body (bats-lang/repository-prototype#487).
   Keyword: text-lint.

     text_lint body BODY HEAD [PHRASES]
                      the findings of the body in the file BODY for the head HEAD (a
                      40-digit commit), one line each on standard output; "ok" when
                      there is none. PHRASES is a file of the phrases the body may not
                      hold, one on each line.
     text_lint event EVENT STATUS URL [PHRASES]
                      the findings of the pull request of the event file EVENT (the
                      JSON GitHub writes for the run) on standard output, and the commit
                      status to post in the file STATUS (a JSON object: state, context
                      text-lint, description, target_url URL). A relock branch and a bot
                      are exempt (success).

   Exit status: 0 done (body: no finding; event: the status is written, whatever its state),
   1 a finding (body) or a file that cannot be read or written or an event that is refused,
   2 the command line is not one of these. It reads the files it is given, makes no network
   call, reads no YAML and no clock. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B
#use env as E
#use result as R

staload "event.sats"
staload "lint.sats"
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

(* The argument at index (the program is 0): where it starts and ends; absent when it starts
   at args_len *)
fn _argument {l:agz}{n:pos}{args_len:nat | args_len <= n}{index:nat}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, index: int index)
  : [start,stop:nat | start <= stop; stop <= args_len] @(int start, int stop) = let
  val start = _skip_arguments(args, args_len, 0, index)
  val stop = find_byte(args, args_len, start, 0)
in @(start, stop) end

(* The file at args[start, stop) read whole, as an array of 524288 bytes and its length; the
   words of the failure when it failed (the array is then empty) *)
fn _read {l:agz}{n:pos | n <= 4096}{stop:nat | stop <= n}{start:nat | start <= stop}
  (args: !$A.borrow(byte, l, n), start: int start, stop: int stop, what: string)
  : @(bool, [m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) = let
  var path : $B.builder(0) = $B.create()
  val () = put_range(args, start, stop, path)
  val @(path_array, path_len) = $B.to_arr(path)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  var text : $B.builder(0) = $B.create()
  val @(ended, words) = read_file(path_view, path_len, text)
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
  val @(array, used) = $B.to_arr(text)
in
  case+ ended of
  | Read_whole() => @(true, array, used)
  | Read_too_long() => let
      val () = prerrln! ("text-lint: the ", what, " file is over 524288 bytes")
    in @(false, array, 0) end
  | Read_failed() => let
      val () = prerrln! ("text-lint: cannot read the ", what, " file: ", words)
    in @(false, array, 0) end
end

(* The phrases file at args[start, stop), or an empty text when start is the end of the
   arguments *)
fn _read_optional {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  {stop:nat | stop <= args_len}{start:nat | start <= stop}
  (args: !$A.borrow(byte, l, n), args_len: int args_len, start: int start, stop: int stop)
  : @(bool, [m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) =
  if start >= args_len then let
    var empty : $B.builder(0) = $B.create()
    val @(array, used) = $B.to_arr(empty)
  in @(true, array, used) end
  else _read(args, start, stop, "phrases")

fn _body {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): int = let
  val @(body_start, body_stop) = _argument(args, args_len, 2)
  val @(head_start, head_stop) = _argument(args, args_len, 3)
  val @(phrases_start, phrases_stop) = _argument(args, args_len, 4)
  val @(extra_start, _) = _argument(args, args_len, 5)
in
  if head_start >= args_len || extra_start < args_len then let
    val () = prerrln! ("usage: text_lint body BODY HEAD [PHRASES]")
  in 2 end
  else let
    val @(body_ok, body_array, body_len) = _read(args, body_start, body_stop, "body")
    val @(phrases_ok, phrases_array, phrases_len) =
      _read_optional(args, args_len, phrases_start, phrases_stop)
    var head : $B.builder(0) = $B.create()
    val () = put_range(args, head_start, head_stop, head)
    val @(head_array, head_len) = $B.to_arr(head)
    val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
    val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
    val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
    val status =
      (if body_ok && phrases_ok then let
         val out = $B.sized_rope_create()
         val count = lint_body(body_view, body_len, head_view, head_len,
           phrases_view, phrases_len, out)
         val () = print_rope(out)
         val () = if count = 0 then println! ("ok") else ()
       in if count = 0 then 0 else 1 end
       else 1): int
    val () = $A.drop<byte>(body_frozen, body_view)
    val () = $A.free<byte>($A.thaw<byte>(body_frozen))
    val () = $A.drop<byte>(phrases_frozen, phrases_view)
    val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
    val () = $A.drop<byte>(head_frozen, head_view)
    val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  in status end
end

fn _event {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): int = let
  val @(event_start, event_stop) = _argument(args, args_len, 2)
  val @(status_start, status_stop) = _argument(args, args_len, 3)
  val @(url_start, url_stop) = _argument(args, args_len, 4)
  val @(phrases_start, phrases_stop) = _argument(args, args_len, 5)
  val @(extra_start, _) = _argument(args, args_len, 6)
in
  if url_start >= args_len || extra_start < args_len then let
    val () = prerrln! ("usage: text_lint event EVENT STATUS URL [PHRASES]")
  in 2 end
  else let
    val @(event_ok, event_array, event_len) = _read(args, event_start, event_stop, "event")
    val @(phrases_ok, phrases_array, phrases_len) =
      _read_optional(args, args_len, phrases_start, phrases_stop)
    var url : $B.builder(0) = $B.create()
    val () = put_range(args, url_start, url_stop, url)
    val @(url_array, url_len) = $B.to_arr(url)
    val @(event_frozen, event_view) = $A.freeze<byte>(event_array)
    val @(phrases_frozen, phrases_view) = $A.freeze<byte>(phrases_array)
    val @(url_frozen, url_view) = $A.freeze<byte>(url_array)
    val status =
      (if event_ok && phrases_ok then let
         val findings = $B.sized_rope_create()
         val status_text = $B.sized_rope_create()
         val code = lint_event(event_view, event_len, phrases_view, phrases_len,
           url_view, url_len, findings, status_text)
         val () = print_rope(findings)
       in
         if code = 0 then let
           var path : $B.builder(0) = $B.create()
           val () = put_range(args, status_start, status_stop, path)
           val @(path_array, path_len) = $B.to_arr(path)
           val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
           val written = write_rope_new_file(path_view, path_len, status_text)
           val () = $A.drop<byte>(path_frozen, path_view)
           val () = $A.free<byte>($A.thaw<byte>(path_frozen))
           val () = if written then () else prerrln! ("text-lint: cannot write the status file")
         in if written then 0 else 1 end
         else let val () = discard_rope(status_text) in 1 end
       end
       else 1): int
    val () = $A.drop<byte>(event_frozen, event_view)
    val () = $A.free<byte>($A.thaw<byte>(event_frozen))
    val () = $A.drop<byte>(phrases_frozen, phrases_view)
    val () = $A.free<byte>($A.thaw<byte>(phrases_frozen))
    val () = $A.drop<byte>(url_frozen, url_view)
    val () = $A.free<byte>($A.thaw<byte>(url_frozen))
  in status end
end

fn _usage (): int = let
  val () = prerrln! ("usage: text_lint body BODY HEAD [PHRASES]")
  val () = prerrln! ("       text_lint event EVENT STATUS URL [PHRASES]")
in 2 end

fn _command {l:agz}{n:pos | n <= 4096}{args_len:nat | args_len <= n}
  (args: !$A.borrow(byte, l, n), args_len: int args_len): int = let
  val @(command_start, command_stop) = _argument(args, args_len, 1)
in
  if command_start >= args_len then _usage()
  else if span_is(args, command_start, command_stop, "body") then _body(args, args_len)
  else if span_is(args, command_start, command_stop, "event") then _event(args, args_len)
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
