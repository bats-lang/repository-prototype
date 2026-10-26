(* fuel -- the fuel of the stream loops of repin (bats-lang/repository-prototype#466).
   Keyword: repin path rule.

   A loop over a stream ends on the end of the file. What makes it total is a fuel of three
   ints (a, b, c) with the lexicographic metric .<a, b, c>.: one unit is spent for each read,
   and the fuel is 2^93 - 1 units at the base 2147483647 (a file offset is an off_t of at most
   63 bits, so this is a platform assumption, not a proof, that no stream is longer). A fuel
   that is gone is a refusal in every loop, never an acceptance, so a counter cannot accept. *)

#include "share/atspre_staload.hats"

(* Whether the fuel (a, b, c) is gone; the result is indexed by the fact, so the else branch
   of a test has a + b + c > 0, which spend needs *)
#pub fn is_gone {a,b,c:nat} (a: int a, b: int b, c: int c): bool (a + b + c <= 0)

implement is_gone (a, b, c) = a + b + c <= 0

(* The fuel after one unit is spent: (a, b, c - 1), or (a, b - 1, base) when c is 0, or
   (a - 1, base, base) when b and c are 0. The type is the proof that it is lexicographically
   smaller, which is what the metric of a loop needs. *)
#pub fn spend {base:pos}{a,b,c:nat | a + b + c > 0}
  (base: int base, a: int a, b: int b, c: int c)
  : [a2,b2,c2:nat | a2 < a || (a2 == a && b2 < b) || (a2 == a && b2 == b && c2 < c)]
    @(int a2, int b2, int c2)

implement spend (base, a, b, c) =
  if c > 0 then @(a, b, c - 1)
  else if b > 0 then @(a, b - 1, base)
  else @(a - 1, base, base)

(* A loop that spends one unit for each step, to show that the compiler takes the three-
   component metric: it counts the units from (a, b, c) down to the end *)
#pub fn units_of {base:pos}{a,b,c:nat} (base: int base, a: int a, b: int b, c: int c): int

fun _units {base:pos}{a,b,c:nat} .<a, b, c>.
  (base: int base, a: int a, b: int b, c: int c, count: int): int =
  if is_gone(a, b, c) then count
  else let
    val @(a2, b2, c2) = spend(base, a, b, c)
  in _units(base, a2, b2, c2, count + 1) end

implement units_of (base, a, b, c) = _units(base, a, b, c, 0)
