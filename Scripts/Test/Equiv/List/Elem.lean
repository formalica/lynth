import Mathlib

/-!
# Alternative definitions: `List.elem`

Six ways to ask whether a value occurs in a list.  `List.elem` is a short-
circuiting recursion on `a == b`; the alternatives are a non-short-circuiting
`foldl`, a `foldr`, `List.count` compared against `0`, `List.filter` with a
`isEmpty` test, an `indexOf`-style `findIdx` with a length guard, and an
`erase`-based test.

Two traps are recorded here.  First, argument order again: `List.elem a l` is
value-first, while `List.contains l a` is list-first.  Second, `List.findIdx`
returns `l.length` — not `0` and not `none` — when the predicate never fires, so
any `findIdx`-based membership test *must* compare against the length; forgetting
the guard reports every element of a singleton list as present.  Membership is
computed with `a == x`, never `x == a`.  Verified against the original on all
lists of length ≤ 3 over `{0, 1, 2}` and all values in that set.
-/

namespace Alt.List.elem

variable {α : Type u}

/-- The original, kept as the reference point.  Value first, as in core. -/
def orig [BEq α] (a : α) (l : List α) : Bool := List.elem a l

/-- Direct recursion with the `a == x` test spelled out, the shape `List.elem`
itself uses.  Note the early exit: a hit stops the search. -/
def direct [BEq α] : α → List α → Bool
  | _, [] => false
  | a, x :: t => if a == x then true else direct a t

/-- A `foldl` that keeps `true` once seen.  Unlike `direct` this does *not*
short-circuit — every element is tested — but the answer is the same.  A
different trade-off, not a different answer. -/
def viaFoldl [BEq α] (a : α) (l : List α) : Bool :=
  l.foldl (fun acc x => acc || (a == x)) false

/-- The same latch driven by `foldr`, so the list is scanned right to left and
the tests are combined on the way out. -/
def viaFoldr [BEq α] (a : α) (l : List α) : Bool :=
  l.foldr (fun x acc => (a == x) || acc) false

/-- Reuse `List.count` — a different library function — and ask whether the count
is positive.  Note `>` on `ℕ`, and that this counts *all* occurrences before
answering, so it is strictly more work than `orig`. -/
def viaCountPos [BEq α] (a : α) (l : List α) : Bool := decide (List.count a l > 0)

/-- `filter` the occurrences, then test the result for emptiness.  Reuses
`List.isEmpty` as the emptiness oracle instead of a pattern match. -/
def viaFilterEmpty [BEq α] (a : α) (l : List α) : Bool :=
  (l.filter fun x => a == x).isEmpty == false

/-- `findIdx` returns `l.length` on failure, so the guard is `≠ l.length`; this
is the trap this file exists to record.  Searching rather than scanning: the
answer is an index comparison, and no counter is threaded. -/
def viaFindIdx [BEq α] (a : α) (l : List α) : Bool :=
  l.findIdx (fun x => a == x) != l.length

/-- Destructive test: if erasing one occurrence empties the list, the value was
the only element, so it was present.  Otherwise recurse on the shortened list.
Decreases on an explicit `ℕ` fuel. -/
def viaErase [BEq α] : ℕ → α → List α → Bool
  | 0, _, _ => false
  | _, _, [] => false
  | n + 1, a, x :: t =>
      let e := (x :: t).erase a
      if e.length < (x :: t).length then true else viaErase n a t

/-- `viaErase` seeded with fuel `l.length` and the value in first position. -/
def viaEraseLoop [BEq α] (a : α) (l : List α) : Bool := viaErase l.length a l

end Alt.List.elem
