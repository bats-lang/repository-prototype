(* event -- the pull request event the text-lint workflow reads
   (bats-lang/repository-prototype#487). Keyword: text-lint event.

   The event is the JSON file GitHub writes for the run (GITHUB_EVENT_PATH). Four strings are
   taken from it, pull_request.body, pull_request.head.sha, pull_request.head.ref and
   pull_request.user.login; a missing or null body is an empty one. The status is the commit
   status the workflow posts: state, context text-lint, a description of ASCII with no quote
   or backslash and at most 140 bytes (the first finding), and the run's URL. A pull request
   of a relock branch (relock/<date>) or of a bot (a login that ends with [bot]) is exempt:
   its status is success and says so. The event is at most 524288 bytes and the body 262144
   decoded bytes; a larger one is refused (the status is not written). *)

#include "share/atspre_staload.hats"

#use array as A
#use arith as AR
#use builder as B
#use json as J
#use result as R

staload "lint.sats"
staload "support.sats"

fun _text_is {l:agz}{cap:pos}{dlen:nat | dlen <= cap}{literal_len:nat | dlen == literal_len}
  {i:nat | i <= dlen} .<dlen - i>.
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len, i: int i): bool =
  if i >= dlen then true
  else if byte2int0($A.get<byte>(text, i)) = char2int0(string_get_at(literal, i)) then
    _text_is(text, dlen, literal, i + 1)
  else false

fn _string_is {l:agz}{cap:pos}{dlen:nat | dlen <= cap}{literal_len:nat}
  (text: !$A.arr(byte, l, cap), dlen: int dlen, literal: string literal_len): bool =
  if dlen = g1u2i(string1_length(literal)) then _text_is(text, dlen, literal, 0) else false

fun _copy_loop {l:agz}{cap:pos}{dlen:nat | dlen <= cap; dlen <= 262144}{i:nat | i <= dlen}
  {used:nat | used + (dlen - i) <= 524288} .<dlen - i>.
  (text: !$A.arr(byte, l, cap), dlen: int dlen, i: int i,
   out: !$B.builder(used) >> $B.builder(used + (dlen - i))): void =
  if i >= dlen then ()
  else let
    val () = $B.put_char(out, $AR.low_byte(byte2int0($A.get<byte>(text, i))))
  in _copy_loop(text, dlen, i + 1, out) end

(* The bytes of a JSON string appended to the empty builder: whether it fits *)
fn _copy_string {l:agz}{cap:pos}{dlen:nat | dlen <= cap}
  (text: !$A.arr(byte, l, cap), dlen: int dlen, out: !$B.builder(0) >> $B.builder_v): bool =
  if dlen <= 262144 then let val () = _copy_loop(text, dlen, 0, out) in true end else false

(* The string value of the field key of the object, copied to the empty builder *)
fun _find_field {fields_size:nat}{key_len:nat} .<fields_size>.
  (fields: !$J.json_entries(fields_size), key: string key_len,
   out: !$B.builder(0) >> $B.builder_v): bool =
  case+ fields of
  | $J.json_entries_nil() => false
  | $J.json_entries_cons(field_key, field_key_len, value, rest) =>
    if _string_is(field_key, field_key_len, key) then
      (case+ value of
       | $J.json_str(text, text_len) => _copy_string(text, text_len, out)
       | _ => false)
    else _find_field(rest, key, out)

(* The same for the field key of the object that is the field first *)
fun _find_in_one {entries_size:nat}{first_len,key_len:nat} .<entries_size>.
  (entries: !$J.json_entries(entries_size), first: string first_len, key: string key_len,
   out: !$B.builder(0) >> $B.builder_v): bool =
  case+ entries of
  | $J.json_entries_nil() => false
  | $J.json_entries_cons(entry_key, entry_key_len, value, rest) =>
    if _string_is(entry_key, entry_key_len, first) then
      (case+ value of
       | $J.json_obj(fields) => _find_field(fields, key, out)
       | _ => false)
    else _find_in_one(rest, first, key, out)

(* The same two objects deep *)
fun _find_in_two {entries_size:nat}{first_len,second_len,key_len:nat} .<entries_size>.
  (entries: !$J.json_entries(entries_size), first: string first_len,
   second: string second_len, key: string key_len,
   out: !$B.builder(0) >> $B.builder_v): bool =
  case+ entries of
  | $J.json_entries_nil() => false
  | $J.json_entries_cons(entry_key, entry_key_len, value, rest) =>
    if _string_is(entry_key, entry_key_len, first) then
      (case+ value of
       | $J.json_obj(fields) => _find_in_one(fields, second, key, out)
       | _ => false)
    else _find_in_two(rest, first, second, key, out)

fun _copy_exact {l,other_loc:agz}{n:pos}{m:nat | m <= n}{capacity:pos | m <= capacity}
  {i:nat | i <= m} .<m - i>.
  (source: !$A.borrow(byte, l, n), m: int m, destination: !$A.arr(byte, other_loc, capacity),
   i: int i): void =
  if i >= m then ()
  else let
    val () = $A.set<byte>(destination, i, $A.read<byte>(source, i))
  in _copy_exact(source, m, destination, i + 1) end

(* The first line of a text to the rope, ASCII only: a quote or a backslash becomes an
   apostrophe, any other byte outside 32 to 126 a question mark; at most cap bytes *)
fun _put_clean {l:agz}{n:pos}{used:nat | used <= n}{i:nat | i <= used}{count:nat} .<used - i>.
  (bytes: !$A.borrow(byte, l, n), used: int used, i: int i, count: int count, cap: int,
   out: !$B.sized_rope): void =
  if i >= used then ()
  else if count >= cap then ()
  else let
    val c = byte2int0($A.read<byte>(bytes, i))
  in
    if c = 10 then ()
    else let
      val () =
        (if c >= 32 && c < 127 && c <> 34 && c <> 92 then $B.sized_rope_copy(out, bytes, i, i + 1)
         else if c = 34 || c = 92 then $B.sized_rope_bput(out, "'")
         else $B.sized_rope_bput(out, "?"))
    in _put_clean(bytes, used, i + 1, count + 1, cap, out) end
  end

(* The first line (140 bytes at most) of the rope, cleaned, to out; the rope is consumed *)
fn _first_finding (text: $B.sized_rope, out: !$B.sized_rope): void =
  case+ $B.sized_rope_chunks(text) of
  | ~$B.rope_sized_nil() => ()
  | ~$B.rope_sized_cons(chunk, used, rest) => let
      val @(frozen, view) = $A.freeze<byte>(chunk)
      val () = _put_clean(view, used, 0, 0, 140, out)
      val () = $A.drop<byte>(frozen, view)
      val () = $A.free<byte>($A.thaw<byte>(frozen))
      val () = $B.rope_sized_list_free(rest)
    in () end

(* The JSON text parsed whole: whether it is one value; the value (null when not) *)
fn _parsed {l:agz}{len:nat | len <= 524288}
  (text: !$A.borrow(byte, l, 524288), len: int len): @(bool, $J.json_v) =
  if len <= 0 then let
    val () = prerrln! ("text-lint: the event text is empty")
  in @(false, $J.json_null()) end
  else let
    val exact = $A.alloc<byte>(len)
    val () = _copy_exact(text, len, exact, 0)
    val @(frozen, view) = $A.freeze<byte>(exact)
    val parsed =
      (case+ $J.parse_text(view, len) of
       | ~$R.err(failure) => let
           val position = $J.parse_error_pos(failure)
           val () = prerrln! ("text-lint: the event text is not JSON, at byte ", position)
         in @(false, $J.json_null()) end
       | ~$R.ok(root) => @(true, root)): @(bool, $J.json_v)
    val () = $A.drop<byte>(frozen, view)
    val () = $A.free<byte>($A.thaw<byte>(frozen))
  in parsed end

(* Appends the status object: state, the description (the first finding, or the words) and
   the URL, both cleaned *)
fn _put_status {ul:agz}{un:pos}{ulen:nat | ulen <= un}{state_len,words_len:nat}
  (state: string state_len, description_words: string words_len, findings: $B.sized_rope,
   url: !$A.borrow(byte, ul, un), ulen: int ulen, status: !$B.sized_rope): void = let
  val () = $B.sized_rope_bput(status, "{\"state\":\"")
  val () = $B.sized_rope_bput(status, state)
  val () = $B.sized_rope_bput(status, "\",\"context\":\"text-lint\",\"description\":\"")
  val () = $B.sized_rope_bput(status, description_words)
  val () = _first_finding(findings, status)
  val () = $B.sized_rope_bput(status, "\",\"target_url\":\"")
  val () = _put_clean(url, ulen, 0, 0, 512, status)
  val () = $B.sized_rope_bput(status, "\"}\n")
in () end

fn _empty_rope (): $B.sized_rope = $B.sized_rope_create()

(* The event's pull request lint: the findings (one line each) appended to findings and
   the status object to status, from the event event[0, len), the phrases and the run's URL.
   0 when it went well (a failing lint is a status of state failure), 1 when the event is
   refused (said on standard error; nothing useful appended). *)
#pub fn lint_event {el,pl,ul:agz}{pn,un:pos}{len:nat | len <= 524288}
  {plen:nat | plen <= pn}{ulen:nat | ulen <= un}
  (event: !$A.borrow(byte, el, 524288), len: int len, phrases: !$A.borrow(byte, pl, pn),
   plen: int plen, url: !$A.borrow(byte, ul, un), ulen: int ulen,
   findings: !$B.sized_rope, status: !$B.sized_rope): int

implement lint_event (event, len, phrases, plen, url, ulen, findings, status) = let
  val @(ok, root) = _parsed(event, len)
in
  if ~ok then let val () = $J.json_free(root) in 1 end
  else
    (case+ root of
     | ~$J.json_obj(entries) => let
         var body : $B.builder(0) = $B.create()
         val _ = _find_in_one(entries, "pull_request", "body", body)
         var sha : $B.builder(0) = $B.create()
         val sha_ok = _find_in_two(entries, "pull_request", "head", "sha", sha)
         var ref : $B.builder(0) = $B.create()
         val ref_ok = _find_in_two(entries, "pull_request", "head", "ref", ref)
         var login : $B.builder(0) = $B.create()
         val login_ok = _find_in_two(entries, "pull_request", "user", "login", login)
         val () = $J.json_entries_free(entries)
         val @(body_array, body_len) = $B.to_arr(body)
         val @(sha_array, sha_len) = $B.to_arr(sha)
         val @(ref_array, ref_len) = $B.to_arr(ref)
         val @(login_array, login_len) = $B.to_arr(login)
         val @(body_frozen, body_view) = $A.freeze<byte>(body_array)
         val @(sha_frozen, sha_view) = $A.freeze<byte>(sha_array)
         val @(ref_frozen, ref_view) = $A.freeze<byte>(ref_array)
         val @(login_frozen, login_view) = $A.freeze<byte>(login_array)
         val status_code =
           (if ~(sha_ok && ref_ok && login_ok) then let
              val () = prerrln! ("text-lint: the event has no pull_request.head.sha, head.ref or user.login")
            in 1 end
            else if is_exempt(ref_view, ref_len, login_view, login_len) then let
              val () = _put_status("success", "exempt: a bot or a relock branch", _empty_rope(),
                url, ulen, status)
            in 0 end
            else let
              val count = lint_body(body_view, body_len, sha_view, sha_len, phrases, plen, findings)
              val again = $B.sized_rope_create()
              val _ = lint_body(body_view, body_len, sha_view, sha_len, phrases, plen, again)
              val () =
                (if count = 0 then _put_status("success", "the PR body is in form", again, url, ulen, status)
                 else _put_status("failure", "", again, url, ulen, status))
            in 0 end): int
         val () = $A.drop<byte>(body_frozen, body_view)
         val () = $A.free<byte>($A.thaw<byte>(body_frozen))
         val () = $A.drop<byte>(sha_frozen, sha_view)
         val () = $A.free<byte>($A.thaw<byte>(sha_frozen))
         val () = $A.drop<byte>(ref_frozen, ref_view)
         val () = $A.free<byte>($A.thaw<byte>(ref_frozen))
         val () = $A.drop<byte>(login_frozen, login_view)
         val () = $A.free<byte>($A.thaw<byte>(login_frozen))
       in status_code end
     | other => let
         val () = $J.json_free(other)
         val () = prerrln! ("text-lint: the event is not an object")
       in 1 end)
end
