import Mathlib

/-!
# Alternative definitions: `List.find?`

`List.find? p l` is the first element of `l` satisfying `p`, or `none`.  Four
other routes:

* `viaFilterHead` — filter and take the head, so the search is a scan that
  builds a whole intermediate list;
* `byRec` — primitive recursion with the test written as `if p a then`;
* `viaGetElemScan` — search over the positions, then read the element back out,
  so the search never touches the list structure directly;
* `byRevFoldl` — scan the list backwards, and latch onto the first success
  (which is the *last* match, not the first), then reverse.

`byRevFoldl` is the one backwards route: it scans the reversed list and lets
the *last* success overwrite the accumulator.  Since the traversal is reversed,
the last success encountered is the leftmost one, so this does give the first
match — it is the `acc`-overwrites version, not the latch version, that would
have returned the last match instead.
-/

namespace Alt.List.find

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (p : α → Bool) (l : List α) : Option α := List.find? p l

/-- Filter and take the head.  `List.head?_filter` is exactly the identity this
route relies on, so the search becomes a full scan that materialises the
matching elements and then discards all but the first. -/
def viaFilterHead (p : α → Bool) (l : List α) : Option α := (List.filter p l).head?

/-- Primitive recursion with the test written as `if p a then`. -/
def byRec (p : α → Bool) : List α → Option α
  | [] => none
  | a :: t => if p a then some a else byRec p t

/-- Search over the positions: enumerate `Fin l.length`, find the first index
whose element passes, and read that element back.  The list structure is never
pattern-matched during the search. -/
def viaGetElemScan (p : α → Bool) (l : List α) : Option α :=
  (List.finRange l.length).find? (fun i => p (l.get i)) |>.map l.get

/-- Scan the list backwards, letting every success overwrite the accumulator.
Because the traversal is reversed, the value that survives is the one furthest to
the left — the first match — so this is a correct backwards scan. -/
def byRevFoldl (p : α → Bool) (l : List α) : Option α :=
  (l.reverse).foldl (fun acc a => if p a then some a else acc) none

end Alt.List.find
