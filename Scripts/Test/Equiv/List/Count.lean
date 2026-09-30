import Mathlib

/-!
# Alternative definitions: `List.count`

Six ways to count occurrences of a value in a list.  `List.count` is one
recursion with a `==` test; the alternatives use a `foldl` counter, a `foldr`
counter, `List.countP` with a `==`-predicate, `filter` plus `length`, `List.elem`
plus a boolean sum, and an "erase one occurrence, repeat" loop.

Note the argument order: `List.count a l` takes the *value first*, unlike
`List.elem`, which also takes the value first, but unlike `List.erase`, which
takes the list first (`l.erase a`).  That inconsistency is the trap in this
file — write the guard in the wrong order and Lean will either reject it or,
worse, accept a `count` of a different thing.  The count is over the `BEq`
comparison `a == x`, never over `x == a`, which matters as soon as `BEq` is not
symmetric.  Verified against the original on all lists of length ≤ 3 over
`{0, 1, 2}` and all values in that set.
-/

namespace Alt.List.count

variable {α : Type u}

/-- The original, kept as the reference point.  Value first, as in core. -/
def orig [BEq α] (a : α) (l : List α) : ℕ := List.count a l

/-- Direct recursion with the `a == x` test spelled out, the shape
`List.count` itself uses. -/
def direct [BEq α] : α → List α → ℕ
  | _, [] => 0
  | a, x :: t => if a == x then direct a t + 1 else direct a t

/-- A `foldl` counter: scan left to right, bumping the accumulator on a hit.  The
recursion is driven by the library rather than written out. -/
def viaFoldl [BEq α] (a : α) (l : List α) : ℕ :=
  l.foldl (fun acc x => if a == x then acc + 1 else acc) 0

/-- The same counter driven by `foldr`, so the list is visited right to left and
the additions are performed on the way out of the recursion. -/
def viaFoldr [BEq α] (a : α) (l : List α) : ℕ :=
  l.foldr (fun x acc => if a == x then acc + 1 else acc) 0

/-- Reuse the sibling counting function `List.countP` with a `==`-predicate:
`countP` is stated over `Bool` predicates, so this is a different library entry
point computing the same number. -/
def viaCountP [BEq α] (a : α) (l : List α) : ℕ := l.countP fun x => a == x

/-- Select-then-measure: `filter` keeps exactly the occurrences, and counting the
survivors is `length`.  Reuses `List.length` as a substep, but the search
(`filter`) and the measure are both new. -/
def viaFilterLength [BEq α] (a : α) (l : List α) : ℕ := (l.filter fun x => a == x).length

/-- Membership plus summation: turn the `Bool` from `List.elem` into `1`/`0` and
add.  Reuses a *different* library function (`elem`) as the search step and
`List.sum` as the measure, so neither `count`'s recursion nor `filter` appears. -/
def viaElemSum [BEq α] (a : α) (l : List α) : ℕ :=
  (l.map fun x => if List.elem a [x] then (1 : ℕ) else 0).sum

/-- "Erase one occurrence, repeat": destructive counting.  Each round removes
the first `a` with `List.erase` (list-first argument order!) and adds one, which
decreases on the length, so it is driven by an explicit `ℕ` fuel. -/
def viaErase [BEq α] : ℕ → α → List α → ℕ
  | 0, _, _ => 0
  | _, _, [] => 0
  | n + 1, a, x :: t =>
      if x == a then
        match (x :: t).erase a with
        | [] => 1
        | r => 1 + viaErase n a r
      else viaErase n a t

/-- `viaErase` seeded with fuel `l.length` and the value in first position. -/
def viaEraseLoop [BEq α] (a : α) (l : List α) : ℕ := viaErase l.length a l

end Alt.List.count
