import Mathlib

/-!
# Alternative definitions: `List.length`

Six ways to count the elements of a list.  `List.length` is one structural
recursion on the list; the alternatives reach the same `ℕ` by folding left,
folding right, mapping to a unit list and summing, counting with `List.countP`,
and by scanning the reversed list.

Every definition here is polymorphic in the element type and never inspects an
element, which is exactly the `O(|l|)` promise `List.length` makes.  So the
"trap" section of `AltNatGcd` has no counterpart: the only way to get this one
wrong is to write `length (l ++ [x]) = length l` or to forget that `[]` counts
`0` and not `1`.
-/

namespace Alt.List.length

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : ℕ := List.length l

/-- Direct structural recursion, exactly the shape `List.length` itself uses. -/
def direct : List α → ℕ
  | [] => 0
  | _ :: t => direct t + 1

/-- Counting with `foldl`, i.e. left to right, threading a `ℕ` counter.  The
recursion is inside the library rather than written out. -/
def viaFoldl (l : List α) : ℕ := l.foldl (fun acc _ => acc + 1) 0

/-- The same counter driven by `foldr`, so the list is visited right to left.
The counter is bumped on the way back *out* of the recursion. -/
def viaFoldr (l : List α) : ℕ := l.foldr (fun _ acc => acc + 1) 0

/-- Map every element to `1` and sum: length as a "sum of unit weights" rather
than a recursion. -/
def viaSumMap (l : List α) : ℕ := (l.map fun _ => (1 : ℕ)).sum

/-- Length via `List.countP` with the constant-`true` predicate: reuse the
counting machinery of a *different* library function. -/
def viaCountP (l : List α) : ℕ := l.countP fun _ => true

/-- Reverse the list first, then count with `foldl`.  Reuses `List.reverse` as
a substep, but the traversal order and the combinator both change. -/
def viaRevFoldl (l : List α) : ℕ := l.reverse.foldl (fun acc _ => acc + 1) 0

end Alt.List.length
