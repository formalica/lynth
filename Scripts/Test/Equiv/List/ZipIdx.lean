import Mathlib

/-!
# Alternative definitions: `List.zipIdx`

`List.zipIdx l` pairs each element of `l` with its position: `0, 1, …`.
Three other routes:

* `byRangeZip` — zip the *position list* `List.range l.length` against `l` and
  swap the components, so the pairing is done by the zip combinator;
* `byFinRangeGet` — enumerate the positions as `Fin l.length` and read the
  element at each, keeping the bound on the index for free;
* `byCounter` — a left fold carrying a counter, consing each pair and reversing
  at the end, so no index list is materialised at all.

Note on the original's signature: `List.zipIdx` carries a legacy
`optParam ℕ 0` offset, so `List.zipIdx l n` numbers from `n`.  The alternatives
here are the offset-`0` forms, and the theorems state `List.zipIdx l = byFoo l`.
-/

namespace Alt.List.zipIdx

universe u

variable {α : Type u}

/-- The original, kept as the reference point.  With the default offset this
numbers from `0`. -/
def orig (l : List α) : List (α × ℕ) := List.zipIdx l

/-- Zip the position list `List.range l.length` against `l` and swap the
components, so the pairing itself is done by `List.zip`. -/
def byRangeZip (l : List α) : List (α × ℕ) :=
  (List.range l.length).zip l |>.map (fun pr => (pr.2, pr.1))

/-- Enumerate the positions as `Fin l.length` and read the element at each one,
keeping the bound on the index, so `List.get` needs no fallback. -/
def byFinRangeGet (l : List α) : List (α × ℕ) :=
  (List.finRange l.length).map (fun i => (l.get i, i.val))

/-- A left fold carrying a counter: cons each pair and reverse at the end.  No
index list is materialised at all — the position is state inside the fold. -/
def byCounter (l : List α) : List (α × ℕ) :=
  (List.foldl (fun (acc, k) a => ((a, k) :: acc, k + 1))
    ([], 0) l).1.reverse

end Alt.List.zipIdx
