(* pattern -- the small pattern language of the phrases file (bats-lang/repository-prototype#487).
   Keyword: text-lint pattern.

   The phrases of bats-lang/quire's tests/static/guidelines/phrases.tsv are regular
   expressions of Python, searched without regard to case. No package of the repository
   matches a regular expression, so this is the matcher, written for what those phrases use
   and nothing else: a pattern is a sequence of atoms, each one of

     a character                         itself
     \s \d \w                            a blank, a digit, a word character
     \b                                  a word edge (matches no character)
     \<c>                                the character c itself (any other escape)
     [...] and [^...]                    a class: characters and the escapes \s \d \w, or
                                         none of them

   and an atom other than \b may be followed by ? (once or not at all), + (once or more) or
   * (any number of times). There is no group and no alternation: a phrase with either is
   written as one pattern for each of its alternatives (the file's lines), which keeps the
   matcher a plain backtracking search and its termination a metric. A pattern is searched
   anywhere in the text. Text and pattern are compared lowercased, so a pattern is written in
   lowercase. Nothing here reads YAML. *)

#include "share/atspre_staload.hats"

#use array as A

staload "support.sats"

fn _low (c: int): int = if c >= 65 && c <= 90 then c + 32 else c

fn _word (c: int): bool =
  (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c = 95

(* Whether the escape \x matches the lowered character c *)
fn _escape_has (x: int, c: int): bool =
  if x = 115 then (c = 32 || c = 9 || c = 10 || c = 13)
  else if x = 100 then (c >= 48 && c <= 57)
  else if x = 119 then _word(c)
  else _low(x) = c

(* The end of a class from i: just after the closing bracket, else the limit *)
fun _close {l:agz}{n:pos}{plim:nat | plim <= n}{i:nat | i <= plim} .<plim - i>.
  (pat: !$A.borrow(byte, l, n), plim: int plim, i: int i): [e:nat | i <= e; e <= plim] int e =
  if i >= plim then i
  else if byte2int0($A.read<byte>(pat, i)) = 93 then i + 1
  else _close(pat, plim, i + 1)

(* The end of the atom that starts at pi *)
fn _atom_end {l:agz}{n:pos}{plim:nat | plim <= n}{pi:nat | pi < plim}
  (pat: !$A.borrow(byte, l, n), plim: int plim, pi: int pi): [e:nat | pi < e; e <= plim] int e = let
  val c = byte2int0($A.read<byte>(pat, pi))
in
  if c = 92 then (if pi + 1 < plim then pi + 2 else pi + 1)
  else if c = 91 then _close(pat, plim, pi + 1)
  else pi + 1
end

(* Whether a character of the class pat[i, stop) is the lowered character c *)
fun _class_has {l:agz}{n:pos}{stop:nat | stop <= n}{i:nat | i <= stop} .<stop - i>.
  (pat: !$A.borrow(byte, l, n), stop: int stop, i: int i, c: int): bool =
  if i >= stop then false
  else let
    val b = byte2int0($A.read<byte>(pat, i))
  in
    if b = 92 then
      (if i + 1 < stop then
         (if _escape_has(byte2int0($A.read<byte>(pat, i + 1)), c) then true
          else _class_has(pat, stop, i + 2, c))
       else (c = 92))
    else if _low(b) = c then true
    else _class_has(pat, stop, i + 1, c)
  end

(* Whether the atom pat[pi, e) matches the lowered character c *)
fn _atom_has {l:agz}{n:pos}{pi,e:nat | pi < e; e <= n}
  (pat: !$A.borrow(byte, l, n), pi: int pi, e: int e, c: int): bool = let
  val b = byte2int0($A.read<byte>(pat, pi))
in
  if b = 92 then
    (if pi + 1 < e then _escape_has(byte2int0($A.read<byte>(pat, pi + 1)), c) else (c = 92))
  else if b = 91 then let
    val closed = (byte2int0($A.read<byte>(pat, e - 1)) = 93): bool
    val stop = (if closed then (if e - 1 > pi then e - 1 else e) else e): [s:nat | pi < s; s <= e] int s
    val negated = (if pi + 1 < stop then byte2int0($A.read<byte>(pat, pi + 1)) = 94 else false): bool
    val start = (if negated then pi + 2 else pi + 1): [s:nat | pi < s; s <= e + 1] int s
    val found = (if start <= stop then _class_has(pat, stop, start, c) else false): bool
  in if negated then ~found else found end
  else _low(b) = c
end

(* The quantifier that follows the atom that ends at e (a question mark, a plus or a star), else
   zero *)
fn _quantifier {l:agz}{n:pos}{plim:nat | plim <= n}{e:nat | e <= plim}
  (pat: !$A.borrow(byte, l, n), plim: int plim, e: int e): int =
  if e < plim then
    (let val q = byte2int0($A.read<byte>(pat, e))
     in if q = 63 || q = 43 || q = 42 then q else 0 end)
  else 0

(* Where the next atom starts: after the atom that ends at e and its quantifier *)
fn _after {l:agz}{n:pos}{plim:nat | plim <= n}{e:nat | e <= plim}
  (pat: !$A.borrow(byte, l, n), plim: int plim, e: int e): [m:nat | e <= m; m <= plim] int m =
  if e < plim then (if _quantifier(pat, plim, e) > 0 then e + 1 else e) else e

(* Whether lo <= ti <= hi is a word edge of the text *)
fn _edge {l:agz}{n:pos}{lo,hi:nat | lo <= hi; hi <= n}{ti:nat | lo <= ti; ti <= hi}
  (text: !$A.borrow(byte, l, n), lo: int lo, hi: int hi, ti: int ti): bool = let
  val before = (if ti > lo then _word(byte2int0($A.read<byte>(text, ti - 1))) else false): bool
  val after = (if ti < hi then _word(byte2int0($A.read<byte>(text, ti))) else false): bool
in before != after end

(* The end of the characters from j on that the atom pat[pi, e) matches *)
fun _span_end {pl,tl:agz}{pn,tn:pos}{hi:nat | hi <= tn}{pi,e:nat | pi < e; e <= pn}
  {j:nat | j <= hi} .<hi - j>.
  (pat: !$A.borrow(byte, pl, pn), pi: int pi, e: int e,
   text: !$A.borrow(byte, tl, tn), hi: int hi, j: int j): [k:nat | j <= k; k <= hi] int k =
  if j >= hi then j
  else if _atom_has(pat, pi, e, _low(byte2int0($A.read<byte>(text, j))))
  then _span_end(pat, pi, e, text, hi, j + 1)
  else j

(* Whether pat[pi, plim) matches the text from ti on (the text is text[lo, hi)) *)
fun _match {pl,tl:agz}{pn,tn:pos}{plim:nat | plim <= pn}{lo,hi:nat | lo <= hi; hi <= tn}
  {pi:nat | pi <= plim}{ti:nat | lo <= ti; ti <= hi} .<plim - pi, hi + 2>.
  (pat: !$A.borrow(byte, pl, pn), plim: int plim, pi: int pi,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi, ti: int ti): bool =
  if pi >= plim then true
  else if byte2int0($A.read<byte>(pat, pi)) = 92 then
    (if pi + 1 < plim then
       (if byte2int0($A.read<byte>(pat, pi + 1)) = 98 then
          (if _edge(text, lo, hi, ti) then _match(pat, plim, pi + 2, text, lo, hi, ti) else false)
        else _atom(pat, plim, pi, text, lo, hi, ti))
     else _atom(pat, plim, pi, text, lo, hi, ti))
  else _atom(pat, plim, pi, text, lo, hi, ti)

(* The atom at pi, which is not an edge, with its quantifier and the rest of the pattern *)
and _atom {pl,tl:agz}{pn,tn:pos}{plim:nat | plim <= pn}{lo,hi:nat | lo <= hi; hi <= tn}
  {pi:nat | pi < plim}{ti:nat | lo <= ti; ti <= hi} .<plim - pi, hi + 1>.
  (pat: !$A.borrow(byte, pl, pn), plim: int plim, pi: int pi,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi, ti: int ti): bool = let
    val e = _atom_end(pat, plim, pi)
    val q = _quantifier(pat, plim, e)
    val next = _after(pat, plim, e)
    in
    if q = 63 then
      (if ti < hi then
         (if _atom_has(pat, pi, e, _low(byte2int0($A.read<byte>(text, ti)))) then
            (if _match(pat, plim, next, text, lo, hi, ti + 1) then true
             else _match(pat, plim, next, text, lo, hi, ti))
          else _match(pat, plim, next, text, lo, hi, ti))
       else _match(pat, plim, next, text, lo, hi, ti))
    else if q = 43 || q = 42 then let
      val j = _span_end(pat, pi, e, text, hi, ti)
      val floor = (if q = 43 then ti + 1 else ti): [f:nat | ti <= f; f <= ti + 1] int f
    in
      if j < floor then false
      else _back(pat, plim, pi, next, text, lo, hi, j, floor)
    end
    else
      (if ti < hi then
         (if _atom_has(pat, pi, e, _low(byte2int0($A.read<byte>(text, ti)))) then
            _match(pat, plim, next, text, lo, hi, ti + 1)
          else false)
       else false)
    end

(* The rest of the pattern from next, after the repeated atom matched the text up to j, then
   to one fewer, down to floor *)
and _back {pl,tl:agz}{pn,tn:pos}{plim:nat | plim <= pn}{lo,hi:nat | lo <= hi; hi <= tn}
  {pi:nat | pi < plim}{next:nat | pi < next; next <= plim}
  {j:nat | j <= hi}{floor:nat | floor <= j; lo <= floor} .<plim - pi, j>.
  (pat: !$A.borrow(byte, pl, pn), plim: int plim, pi: int pi, next: int next,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi, j: int j, floor: int floor): bool =
  if _match(pat, plim, next, text, lo, hi, j) then true
  else if j > floor then _back(pat, plim, pi, next, text, lo, hi, j - 1, floor)
  else false

fun _search {pl,tl:agz}{pn,tn:pos}{plim:nat | plim <= pn}{pstart:nat | pstart <= plim}
  {lo,hi:nat | lo <= hi; hi <= tn}{ti:nat | lo <= ti; ti <= hi} .<hi - ti>.
  (pat: !$A.borrow(byte, pl, pn), plim: int plim, pstart: int pstart,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi, ti: int ti)
  : [p:int | p < 0 || (lo <= p && p <= hi)] int p =
  if _match(pat, plim, pstart, text, lo, hi, ti) then ti
  else if ti >= hi then ~1
  else _search(pat, plim, pstart, text, lo, hi, ti + 1)

(* Where the pattern pat[pstart, plim) first matches the text text[lo, hi): that place, else
   a negative number *)
#pub fn pattern_search {pl,tl:agz}{pn,tn:pos}{plim:nat | plim <= pn}{pstart:nat | pstart <= plim}
  {lo,hi:nat | lo <= hi; hi <= tn}
  (pat: !$A.borrow(byte, pl, pn), plim: int plim, pstart: int pstart,
   text: !$A.borrow(byte, tl, tn), lo: int lo, hi: int hi)
  : [p:int | p < 0 || (lo <= p && p <= hi)] int p

implement pattern_search (pat, plim, pstart, text, lo, hi) =
  _search(pat, plim, pstart, text, lo, hi, lo)
