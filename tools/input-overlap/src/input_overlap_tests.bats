(* input_overlap_tests -- the tests of input-overlap (bats-lang/repository-prototype#544), run by
   `bats test` in tools/input-overlap. Each case gives the text of a file in the base, the head and the
   old checkout and the number of inputs removed wrongly. Keyword: input-overlap tests. *)

#include "share/atspre_staload.hats"

#use array as A
#use builder as B

staload "inputs.sats"
staload "overlap.sats"
staload "support.sats"

fn _text {text_len:nat | text_len < 4096} (text: string text_len)
  : @([m:agz] $A.arr(byte, m, $B.BUILDER_CAP), [k:nat | k <= $B.BUILDER_CAP] int k) = let
  var builder : $B.builder(0) = $B.create()
  val () = $B.bput(builder, text)
in $B.to_arr(builder) end

(* Whether the inputs removed from base to head, given old, are that many (the kind is the file's) *)
fn _removed_is {base_len,head_len,old_len:nat | base_len < 4096; head_len < 4096; old_len < 4096}
  (kind: file_kind, base: string base_len, head: string head_len, old: string old_len, expected: int): bool = let
  val @(base_array, base_used) = _text(base)
  val @(head_array, head_used) = _text(head)
  val @(old_array, old_used) = _text(old)
  val @(path_array, path_used) = _text("fixture.yml")
  val @(base_frozen, base_view) = $A.freeze<byte>(base_array)
  val @(head_frozen, head_view) = $A.freeze<byte>(head_array)
  val @(old_frozen, old_view) = $A.freeze<byte>(old_array)
  val @(path_frozen, path_view) = $A.freeze<byte>(path_array)
  val got = removed_inputs(base_view, base_used, head_view, head_used, old_view, old_used, kind,
    path_view, 0, path_used)
  val () = $A.drop<byte>(base_frozen, base_view)
  val () = $A.free<byte>($A.thaw<byte>(base_frozen))
  val () = $A.drop<byte>(head_frozen, head_view)
  val () = $A.free<byte>($A.thaw<byte>(head_frozen))
  val () = $A.drop<byte>(old_frozen, old_view)
  val () = $A.free<byte>($A.thaw<byte>(old_frozen))
  val () = $A.drop<byte>(path_frozen, path_view)
  val () = $A.free<byte>($A.thaw<byte>(path_frozen))
in got = expected end

fn _kind_is_action {path_len:nat | path_len < 4096} (path: string path_len): bool = let
  val @(array, used) = _text(path)
  val @(frozen, view) = $A.freeze<byte>(array)
  val kind = file_kind_of(view, 0, used)
  val answer = (case+ kind of | Action_file() => true | _ => false): bool
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in answer end

fn _kind_is_workflow {path_len:nat | path_len < 4096} (path: string path_len): bool = let
  val @(array, used) = _text(path)
  val @(frozen, view) = $A.freeze<byte>(array)
  val kind = file_kind_of(view, 0, used)
  val answer = (case+ kind of | Workflow_file() => true | _ => false): bool
  val () = $A.drop<byte>(frozen, view)
  val () = $A.free<byte>($A.thaw<byte>(frozen))
in answer end

fn _action_both (): string 161 = "name: setup\ninputs:\n  node-version:\n    description: The Node version\n    required: false\n  other:\n    description: Another\nruns:\n  using: composite\n  steps: []\n"

$UNITTEST.run begin

(* the kinds of path the check reads *)
fn test_kinds_of_path (): bool =
  _kind_is_action("action.yml") && _kind_is_action("action.yaml")
  && _kind_is_action(".github/actions/setup/action.yml") && _kind_is_action("e2e-setup/action.yaml")
  && _kind_is_workflow(".github/workflows/check.yml") && _kind_is_workflow(".github/workflows/x.yaml")
  && not(_kind_is_action("src/reaction.yml")) && not(_kind_is_workflow("src/check.yml"))
  && not(_kind_is_workflow(".github/workflows/readme.md")) && not(_kind_is_action("README.md"))

(* an input removed from an action, with nothing before it, is refused *)
fn test_action_input_removed (): bool =
  _removed_is(Action_file(), "inputs:\n  node-version:\n    description: v\n  other:\n    description: o\nruns:\n  using: composite\n",
    "inputs:\n  other:\n    description: o\nruns:\n  using: composite\n",
    "inputs:\n  node-version:\n    description: v\n  other:\n    description: o\nruns:\n  using: composite\n", 1)

(* the pwa#136 change: node-version replaced by node-version-file, a rename, is a removal *)
fn test_action_input_renamed (): bool =
  _removed_is(Action_file(), "inputs:\n  node-version:\n    description: v\n",
    "inputs:\n  node-version-file:\n    description: f\n",
    "inputs:\n  node-version:\n    description: v\n", 1)

(* every input removed: the head file has none or is not there *)
fn test_action_removed_whole (): bool =
  _removed_is(Action_file(), "inputs:\n  a:\n    description: x\n  b:\n    description: y\n", "", "inputs:\n  a:\n    description: x\n", 2)

(* inputs kept, added, reordered or changed in their properties are not removed *)
fn test_action_input_kept_or_added (): bool =
  _removed_is(Action_file(), _action_both(), _action_both(), _action_both(), 0)
  && _removed_is(Action_file(), "inputs:\n  a:\n    description: x\n",
       "inputs:\n  b:\n    description: y\n  a:\n    description: changed\n    default: z\n", "", 0)
  && _removed_is(Action_file(), "", "inputs:\n  a:\n    description: x\n", "", 0)

(* an input the default branch had marked deprecated a cycle ago may go; one marked less than a cycle ago may not *)
fn test_action_deprecated_input_removal (): bool =
  _removed_is(Action_file(), "inputs:\n  a:\n    description: Deprecated: use b\n  b:\n    description: x\n",
    "inputs:\n  b:\n    description: x\n",
    "inputs:\n  a:\n    description: Deprecated: use b\n  b:\n    description: x\n", 0)
  && _removed_is(Action_file(), "inputs:\n  a:\n    description: Deprecated: use b\n  b:\n    description: x\n",
       "inputs:\n  b:\n    description: x\n",
       "inputs:\n  a:\n    description: x\n  b:\n    description: x\n", 1)
  && _removed_is(Action_file(), "inputs:\n  a:\n    description: \"Deprecated: use b\"\n",
       "", "inputs:\n  a:\n    description: 'Deprecated: use b'\n", 0)
  && _removed_is(Action_file(), "inputs:\n  a:\n    deprecationMessage: use b\n    description: x\n",
       "", "inputs:\n  a:\n    description: x\n    deprecationMessage: use b\n", 0)
  && _removed_is(Action_file(), "inputs:\n  a:\n    description: x\n", "", "inputs:\n  a:\n    description: A Deprecated word later\n", 1)

(* a reusable workflow: the inputs of workflow_call are read, not those of workflow_dispatch or of a job *)
fn test_workflow_inputs (): bool =
  _removed_is(Workflow_file(),
    "name: w\non:\n  workflow_call:\n    inputs:\n      tools-ref:\n        type: string\n      other:\n        type: string\njobs:\n  j:\n    runs-on: x\n",
    "name: w\non:\n  workflow_call:\n    inputs:\n      other:\n        type: string\njobs:\n  j:\n    runs-on: x\n",
    "name: w\non:\n  workflow_call:\n    inputs:\n      tools-ref:\n        type: string\n      other:\n        type: string\n", 1)
  && _removed_is(Workflow_file(),
       "on:\n  workflow_dispatch:\n    inputs:\n      refusal:\n        type: string\n  workflow_call:\n    inputs:\n      kept:\n        type: string\n",
       "on:\n  workflow_dispatch:\n  workflow_call:\n    inputs:\n      kept:\n        type: string\n",
       "", 0)
  && _removed_is(Workflow_file(),
       "on:\n  push:\n    branches: [main]\njobs:\n  j:\n    with:\n      inputs:\n        a: b\n",
       "on:\n  push:\n    branches: [main]\n", "", 0)
  && _removed_is(Workflow_file(),
       "on:\n  workflow_call:\n    inputs:\n      a:\n        description: Deprecated, use b\n        type: string\n    secrets:\n      token:\n        required: true\n",
       "on:\n  workflow_call:\n    secrets:\n      token:\n        required: true\n",
       "on:\n  workflow_call:\n    inputs:\n      a:\n        description: Deprecated, use b\n        type: string\n", 0)

(* quoted keys, comments and blank lines between inputs *)
fn test_forms_of_keys (): bool =
  _removed_is(Workflow_file(),
    "on:\n  workflow_call:\n    inputs:\n      # first\n      \"quoted\":\n        type: string\n\n      'single':\n        type: string\n",
    "on:\n  workflow_call:\n    inputs:\n      single:\n        type: string\n", "", 1)
  && _removed_is(Action_file(), "inputs:\n  a-b_c:\n    description: x\n  d.e:\n    description: y\n",
       "inputs:\n  a-b_c:\n    description: x\n  d.e:\n    description: y\n", "", 0)

end
