(* inputs -- the inputs an action or a reusable workflow declares
   (bats-lang/repository-prototype#544). Keyword: input-overlap inputs.

   The file is read as lines (indentation and keys), not as YAML, as gated.bats of text-lint reads
   the triggers of a workflow. The inputs of

     an action.yml        the keys under the top-level `inputs:` (indent 0)
     a reusable workflow  the keys under `on:` > `workflow_call:` > `inputs:`

   `workflow_dispatch:` inputs are the dispatcher's, not a caller's `with:`, and are not read. An input
   is deprecated when its block has a `deprecationMessage:` key (GitHub's own: the runner logs it as
   a warning when a caller sets the input) or a `description:` on one line that starts with
   Deprecated (a reusable workflow has no deprecationMessage). A key may be quoted. The
   inputs are numbered from 0 in the order of the file; input_at answers the k-th. *)

#include "share/atspre_staload.hats"

#use array as A

staload "support.sats"

(* What a path is, to this check: the file of an action, of a workflow that may be reusable,
   or neither *)
#pub datatype file_kind =
  | Action_file
  | Workflow_file
  | Not_interface

fun _skip_spaces {l:agz}{n:pos}{limit:nat | limit <= n}{i:nat | i <= limit} .<limit - i>.
  (text: !$A.borrow(byte, l, n), limit: int limit, i: int i): [j:nat | i <= j; j <= limit] int j =
  if i >= limit then i
  else if byte2int0($A.read<byte>(text, i)) = 32 then _skip_spaces(text, limit, i + 1)
  else i

(* Whether the bytes of path[start, stop) end with the literal *)
fn _ends_with {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}{literal_len:nat}
  (path: !$A.borrow(byte, l, n), start: int start, stop: int stop, literal: string literal_len): bool =
  if stop - start >= g1u2i(string1_length(literal)) then
    span_is(path, stop - g1u2i(string1_length(literal)), stop, literal)
  else false

(* Whether path[start, stop) names a file with the same name as the literal, at the start or after a / *)
fn _is_named {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}{literal_len:nat}
  (path: !$A.borrow(byte, l, n), start: int start, stop: int stop, literal: string literal_len): bool =
  if span_is(path, start, stop, literal) then true
  else if stop - start > g1u2i(string1_length(literal)) then
    (if _ends_with(path, start, stop, literal) then
       byte2int0($A.read<byte>(path, stop - g1u2i(string1_length(literal)) - 1)) = 47
     else false)
  else false

(* The kind of the path path[start, stop): action.yml or action.yaml (at the root or in a directory),
   or a .yml or .yaml file under .github/workflows/ *)
#pub fn file_kind_of {l:agz}{n:pos}{stop:nat | stop <= n}{start:nat | start <= stop}
  (path: !$A.borrow(byte, l, n), start: int start, stop: int stop): file_kind

implement file_kind_of (path, start, stop) =
  if _is_named(path, start, stop, "action.yml") || _is_named(path, start, stop, "action.yaml") then Action_file()
  else if starts_with(path, stop, start, ".github/workflows/")
          && (_ends_with(path, start, stop, ".yml") || _ends_with(path, start, stop, ".yaml")) then Workflow_file()
  else Not_interface()

(* How far the levels reach: 3 inside inputs, 2 inside workflow_call (an action starts here), 1
   inside on, 0 outside. The line of indent d leaves every level whose key is at that indent or deeper. *)
fun _pop {level:nat | level <= 3} .<level>.
  (level: int level, d: int, indent_on: int, indent_call: int, indent_inputs: int)
  : [r:nat | r <= level] int r =
  if level <= 0 then 0
  else if level >= 3 then
    (if d <= indent_inputs then _pop(2, d, indent_on, indent_call, indent_inputs) else 3)
  else if level >= 2 then
    (if d <= indent_call then _pop(1, d, indent_on, indent_call, indent_inputs) else 2)
  else (if d <= indent_on then 0 else 1)

(* The input the scan has finished, when it is the k-th *)
fn _finished {len:nat}{cs,ce:nat | cs <= ce; ce <= len}
  (len: int len, have: int, count: int, k: int, cs: int cs, ce: int ce, deprecated: bool)
  : [a,b:nat | a <= b; b <= len] @(bool, int a, int b, bool) =
  if have > 0 && count - 1 = k then @(true, cs, ce, deprecated) else @(false, 0, 0, false)

(* Whether the value after a colon at text[value, line_stop) starts with Deprecated, in quotes or not *)
fn _value_deprecated {l:agz}{n:pos}{line_stop:nat | line_stop <= n}{value:nat | value <= line_stop}
  (text: !$A.borrow(byte, l, n), line_stop: int line_stop, value: int value): bool =
  if value >= line_stop then false
  else let
    val first = byte2int0($A.read<byte>(text, value))
  in
    if first = 34 || first = 39 then starts_with(text, line_stop, value + 1, "Deprecated")
    else starts_with(text, line_stop, value, "Deprecated")
  end

(* The end of the name whose colon is at colon: before a closing quote that matches the opening one *)
fn _unquote {l:agz}{n:pos}{key_start:nat}{colon:nat | key_start <= colon; colon <= n}
  (text: !$A.borrow(byte, l, n), key_start: int key_start, colon: int colon, first: int, quoted: bool)
  : [e:nat | key_start <= e; e <= colon] int e =
  if quoted then
    (if colon > key_start then
       (if byte2int0($A.read<byte>(text, colon - 1)) = first then colon - 1 else colon)
     else colon)
  else colon

(* The key of the line whose content starts at text[content] (before line_stop): whether there is
   one (a name, optionally quoted, and a colon), where its name starts and stops, and where the value after the colon starts *)
fn _key_span {l:agz}{n:pos}{line_stop:nat | line_stop <= n}{content:nat | content < line_stop}
  (text: !$A.borrow(byte, l, n), line_stop: int line_stop, content: int content)
  : [s,e,v:nat | s <= e; e <= line_stop; v <= line_stop] @(bool, int s, int e, int v) = let
  val first = byte2int0($A.read<byte>(text, content))
  val quoted = (first = 34 || first = 39): bool
  val key_start = (if quoted then content + 1 else content): [s:nat | s <= line_stop] int s
  val colon = find_byte(text, line_stop, key_start, 58)
in
  if colon >= line_stop then @(false, 0, 0, 0)
  else let
    val key_stop = _unquote(text, key_start, colon, first, quoted)
    val value = _skip_spaces(text, line_stop, colon + 1)
  in @(true, key_start, key_stop, value) end
end

fun _scan {l:agz}{n:pos}{len:nat | len <= n}{pos:nat | pos <= len}{level:nat | level <= 3}
  {cs,ce:nat | cs <= ce; ce <= len} .<len - pos>.
  (text: !$A.borrow(byte, l, n), len: int len, pos: int pos, kind: file_kind, k: int,
   level: int level, indent_on: int, indent_call: int, indent_inputs: int, child: int,
   count: int, have: int, cs: int cs, ce: int ce, deprecated: bool)
  : [a,b:nat | a <= b; b <= len] @(bool, int a, int b, bool) =
  if pos >= len then _finished(len, have, count, k, cs, ce, deprecated)
  else let
    val line_stop = find_byte(text, len, pos, 10)
    val next = (if line_stop >= len then len else line_stop + 1): [m:nat | m <= len; pos < m] int m
    val content = _skip_spaces(text, line_stop, pos)
  in
    if content >= line_stop then
      _scan(text, len, next, kind, k, level, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
    else let
      val first = byte2int0($A.read<byte>(text, content))
    in
      if first = 35 || first = 45 then
        _scan(text, len, next, kind, k, level, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
      else let
        val @(has_key, key_start, key_stop, value) = _key_span(text, line_stop, content)
      in
        if not(has_key) then
          _scan(text, len, next, kind, k, level, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
        else let
          val d = content - pos
          val now = _pop(level, d, indent_on, indent_call, indent_inputs)
        in
          if level >= 3 && now < 3 && have > 0 && count - 1 = k then @(true, cs, ce, deprecated)
          else if now = 0 then
            (case+ kind of
             | Action_file() => _scan(text, len, next, kind, k, now, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
             | _ =>
               if d = 0 && span_is(text, key_start, key_stop, "on") then
                 _scan(text, len, next, kind, k, 1, d, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
               else
                 _scan(text, len, next, kind, k, now, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated))
          else if now = 1 then
            (if span_is(text, key_start, key_stop, "workflow_call") then
               _scan(text, len, next, kind, k, 2, indent_on, d, indent_inputs, child, count, have, cs, ce, deprecated)
             else
               _scan(text, len, next, kind, k, now, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated))
          else if now = 2 then
            (if span_is(text, key_start, key_stop, "inputs") then
               (case+ kind of
                | Action_file() =>
                  if d = 0 then
                    _scan(text, len, next, kind, k, 3, indent_on, indent_call, d, 0 - 1, count, 0, 0, 0, false)
                  else
                    _scan(text, len, next, kind, k, now, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated)
                | _ =>
                  _scan(text, len, next, kind, k, 3, indent_on, indent_call, d, 0 - 1, count, 0, 0, 0, false))
             else
               _scan(text, len, next, kind, k, now, indent_on, indent_call, indent_inputs, child, count, have, cs, ce, deprecated))
          else let
            (* inside inputs: the first indent below it is the indent of the inputs *)
            val child_now = (if child < 0 then d else child): int
          in
            if d = child_now then
              (if have > 0 && count - 1 = k then @(true, cs, ce, deprecated)
               else
                 _scan(text, len, next, kind, k, 3, indent_on, indent_call, indent_inputs, child_now, count + 1, 1, key_start, key_stop, false))
            else if d > child_now && have > 0 then
              (if span_is(text, key_start, key_stop, "deprecationMessage") then
                 _scan(text, len, next, kind, k, 3, indent_on, indent_call, indent_inputs, child_now, count, have, cs, ce, true)
               else if span_is(text, key_start, key_stop, "description") && _value_deprecated(text, line_stop, value) then
                 _scan(text, len, next, kind, k, 3, indent_on, indent_call, indent_inputs, child_now, count, have, cs, ce, true)
               else
                 _scan(text, len, next, kind, k, 3, indent_on, indent_call, indent_inputs, child_now, count, have, cs, ce, deprecated))
            else
              _scan(text, len, next, kind, k, 3, indent_on, indent_call, indent_inputs, child_now, count, have, cs, ce, deprecated)
          end
        end
      end
    end
  end

(* The k-th input (from 0) of the text[0, len) of a file of that kind: whether it is there, where its name
   is (start, stop) and whether it is marked deprecated *)
#pub fn input_at {l:agz}{n:pos}{len:nat | len <= n}
  (text: !$A.borrow(byte, l, n), len: int len, kind: file_kind, k: int)
  : [a,b:nat | a <= b; b <= len] @(bool, int a, int b, bool)

implement input_at (text, len, kind, k) =
  (case+ kind of
   | Action_file() => _scan(text, len, 0, kind, k, 2, 0 - 1, 0 - 1, 0 - 1, 0 - 1, 0, 0, 0, 0, false)
   | _ => _scan(text, len, 0, kind, k, 0, 0 - 1, 0 - 1, 0 - 1, 0 - 1, 0, 0, 0, 0, false))

(* Whether a file declares an input, and whether that one is marked deprecated *)
#pub datatype input_state =
  | Input_absent
  | Input_kept
  | Input_deprecated

fun _find {l:agz}{n:pos}{len:nat | len <= n}{k:nat | k <= len}
  {name_loc:agz}{name_size:pos}{name_stop:nat | name_stop <= name_size}{name_start:nat | name_start <= name_stop}
  .<len - k>.
  (text: !$A.borrow(byte, l, n), len: int len, kind: file_kind, k: int k,
   names: !$A.borrow(byte, name_loc, name_size), name_start: int name_start, name_stop: int name_stop)
  : input_state =
  if k >= len then Input_absent()
  else let
    val @(found, start, stop, deprecated) = input_at(text, len, kind, k)
  in
    if found then
      (if spans_equal(text, start, stop, names, name_start, name_stop) then
         (if deprecated then Input_deprecated() else Input_kept())
       else _find(text, len, kind, k + 1, names, name_start, name_stop))
    else Input_absent()
  end

(* The state of the input named names[name_start, name_stop) in the text[0, len) *)
#pub fn find_input {l:agz}{n:pos}{len:nat | len <= n}
  {name_loc:agz}{name_size:pos}{name_stop:nat | name_stop <= name_size}{name_start:nat | name_start <= name_stop}
  (text: !$A.borrow(byte, l, n), len: int len, kind: file_kind,
   names: !$A.borrow(byte, name_loc, name_size), name_start: int name_start, name_stop: int name_stop)
  : input_state

implement find_input (text, len, kind, names, name_start, name_stop) =
  _find(text, len, kind, 0, names, name_start, name_stop)
