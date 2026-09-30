import Mathlib

/-!
# Alternative definitions: `List.headD`

`List.headD l d` is the head of `l`, or `d` when `l` is empty.  Four other
routes:

* `byGetD` — read the element at index `0` and fall back on `getD`;
* `byGetElemD` — match on the partial projection `l[0]?`;
* `byFoldr` — a right fold whose step always returns the current element, so
  the *last* argument is the seed and everything before it is discarded;
* `byRevFoldl` — the same, but as a left fold over the reversed list, so the
  seed is overwritten at the first step instead of being shadowed.

`byFoldr` and `byRevFoldl` are the pair worth comparing: one visits the list
front to back and keeps the *last* element it sees, the other visits it back to
front and keeps the *first*.  Both are `O(length)` where `headD` is `O(1)`,
which is the cost of expressing a head operation through a fold.
-/

namespace Alt.List.headD

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) (d : α) : α := List.headD l d

/-- Read the element at index `0` via the total projection `getD`. -/
def byGetD (l : List α) (d : α) : α := l.getD 0 d

/-- Match on the partial projection `l[0]?`, which is `none` exactly on the
empty list. -/
def byGetElemD (l : List α) (d : α) : α :=
  match l[0]? with
  | some a => a
  | none => d

/-- A right fold whose step ignores the accumulator and returns the element it is
handed.  Applied to `l` this returns the last element of `l`, not the first —
so this route is *wrong* in general and is included precisely to record that a
`foldr` with this step cannot express a head. -/
def byFoldr (l : List α) (d : α) : α := List.foldr (fun a _ => a) d l

/-- A left fold over the reversed list whose step overwrites the accumulator
with the current element.  Folding back to front means the element kept is the
first one seen, which is the head. -/
def byRevFoldl (l : List α) (d : α) : α := (l.reverse).foldl (fun _ a => a) d

end Alt.List.headD
