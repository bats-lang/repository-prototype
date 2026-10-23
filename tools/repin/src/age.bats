(* age -- the release age rule of repin (bats-lang/repository-prototype#410).
   Keyword: repin age.

   A release is a candidate only when it was published at least 7 days
   (604800 seconds) before now. `now` is always an argument, never read from
   the clock inside the logic, so a fixture is exact, and no file's time is
   read. A time is whole seconds since the epoch, a long (64 bits), so the
   rule has no year 2038. *)

#include "share/atspre_staload.hats"

#use array as A

(* The age a release must have, in seconds *)
#pub fn minimum_age_seconds (): lint

implement minimum_age_seconds () = 604800L

(* Whether a release published at published is a candidate at now: it is at
   least the minimum age old. A release from the future is not. *)
#pub fn is_candidate (now: lint, published: lint): bool

implement is_candidate (now, published) = now - published >= 604800L

(* The release's age in whole days at now (the seconds divided by 86400,
   rounded down); 0 for a release published after now *)
#pub fn age_days (now: lint, published: lint): int

implement age_days (now, published) =
  if now - published <= 0L then 0 else g0int2int_lint_int((now - published) / 86400L)

(* A time in seconds is 1 to 12 decimal digits (a year after 30000 is
   outside the rule), so the value never overflows a long *)
fun _digits_value {l:agz}{n:pos}{i,j:nat | i <= j; j <= n} .<j - i>.
  (text: !$A.borrow(byte, l, n), i: int i, j: int j, value: lint): @(bool, lint) =
  if i >= j then @(true, value)
  else let
    val digit = byte2int0($A.read<byte>(text, i))
  in
    if digit >= 48 && digit <= 57 then
      _digits_value(text, i + 1, j, value * 10L + g0int2int_int_lint(digit - 48))
    else @(false, 0L)
  end

(* The number written as the decimal digits text[i, j): whether it is 1 to 12
   digits, and its value *)
#pub fn parse_seconds {l:agz}{n:pos}{i,j:nat | i <= j; j <= n}
  (text: !$A.borrow(byte, l, n), i: int i, j: int j): @(bool, lint)

implement parse_seconds (text, i, j) =
  if j - i >= 1 && j - i <= 12 then _digits_value(text, i, j, 0L)
  else @(false, 0L)
