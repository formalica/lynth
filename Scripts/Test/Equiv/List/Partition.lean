import Mathlib

/-!
# Alternative definitions: `List.partition`

`List.partition p l` splits `l` into the elements satisfying `p` and those that
do not, keeping the original order in each half.  Four other routes:

* `viaTwoFilters` — two independent `List.filter` calls, one per half, so the
  list is scanned twice;
* `viaFilterMapPair` — two `List.filterMap` calls, turning "keep or drop" into
  "some or nothing" in each direction;
* `byFoldl` — a single left fold carrying the pair of halves, appending to
  whichever half is selected;
* `byRevFoldl` — the same idea run over the reversed list with cons into both
  halves, finished by one `reverse` per half.

`byFoldl` and `byRevFoldl` are the pair worth comparing: one pays `O(n²)` for the
`++` in the step, the other is linear and restores the order with two
reversals.
-/

namespace Alt.List.partition

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (p : α → Bool) (l : List α) : List α × List α := List.partition p l

/-- Two independent `List.filter` calls, one per half, so `l` is scanned twice.
-/
def viaTwoFilters (p : α → Bool) (l : List α) : List α × List α :=
  (List.filter p l, List.filter (fun a => !(p a)) l)

/-- Two `List.filterMap` calls: "keep or drop" restated as "some or nothing" in
each direction. -/
def viaFilterMapPair (p : α → Bool) (l : List α) : List α × List α :=
  (List.filterMap (fun a => if p a then some a else none) l,
    List.filterMap (fun a => if p a then none else some a) l)

/-- A single left fold carrying the pair of halves, appending each element to
whichever half the predicate selects.  One pass, at the price of an `++` in the
step. -/
def byFoldl (p : α → Bool) (l : List α) : List α × List α :=
  List.foldl (fun (ys, ns) a => if p a then (ys ++ [a], ns) else (ys, ns ++ [a]))
    ([], []) l

/-- The same, run over the reversed list with cons into both halves.  Because the
traversal is reversed, consing onto the front already reproduces the original
order and no `reverse` is needed — unlike `byFoldl`, this one is linear. -/
def byRevFoldl (p : α → Bool) (l : List α) : List α × List α :=
  let r := List.foldl (fun (ys, ns) a =>
      if p a then (a :: ys, ns) else (ys, a :: ns))
    ([], []) (l.reverse)
  (r.1, r.2)

end Alt.List.partition
