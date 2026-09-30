import Mathlib

/-!
# Alternative definitions: `List.eraseDups`

`List.eraseDups l` is `l` with every element removed that is `==` to an element
kept earlier, so the *first* occurrence of each value survives and the order is
preserved.  Two other routes:

* `byFoldlRev` — a left fold that conses an element unless it is already in the
  accumulator, finished by one `reverse`;
* `viaFilterDups` — recursion that *filters* the tail with `!(b == a)` instead of
  erasing, which is the equation `List.eraseDups_cons` actually states.

Both must test with `==` and not with `∈`: with a `BEq` that is not lawful
the propositional membership `a ∈ acc` and the test `b == a` can disagree, and
only the latter matches what `eraseDups` deletes.

**A trap worth recording.**  The obvious third route — recurse on the head and
`erase` it from the tail — is *wrong*: `List.erase` removes only the **first**
match, so `erase [1, 1, 2] 1 = [1, 2]` still contains a `1`, while
`eraseDups` must leave none.  The tail has to be *filtered*, not erased.
-/

namespace Alt.List.eraseDups

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig [BEq α] (l : List α) : List α := l.eraseDups

/-- A left fold that conses an element unless one already in the accumulator
compares equal to it, finished by one `reverse`.  Membership is checked with
`List.any` and `==`, matching the original's test. -/
def byFoldlRev [BEq α] (l : List α) : List α :=
  (List.foldl (fun acc a =>
    if List.any acc (fun b => b == a) then acc else a :: acc)
    ([] : List α) l).reverse

/-! A fourth route — a latch-armed fold over the *reversed* list, keeping the first
occurrence of each value — was drafted here and then deleted: it is **false**, and
the docstring it carried claimed the opposite.

    byRevFoldlFirst ([1,2,1] : List Nat) = [2,1]
    [1,2,1] |> List.eraseDups            = [1,2]

The reason is a direction error that the reversed traversal makes fatal rather
than cosmetic.  Folding over `l.reverse` visits elements right to left, so the
latch `seen` arms on the **last** copy of each value, not the first; and because
each survivor is consed onto the front, the accumulator reads in reverse order of
traversal — which is the original order, but of the *last* occurrences.  Keeping
first occurrences and traversing right to left are incompatible for a one-pass
latch: by the time the latch sees the leftmost copy, it has already committed to
the rightmost one.

Nothing in the same shape can be repaired, because the two requirements
("first occurrence wins") and ("visit right to left") force the latch to fire on
the wrong element.  The single-pass first-occurrence route is `byFoldlRev`, which
traverses left to right precisely so that the latch arms on the first copy.
-/

/-- Fuel for `viaFilterDups`.  Carrying the remaining length explicitly is not
decoration: `List.filter` is compiled through `brecOn`, so a recursion whose
argument is a `List.filter` result cannot be recognised as structural and would
have to be discharged by well-founded recursion.  The fuel is decreased by one at
each step, and the caller supplies `l.length`, which is one more than the tail's
length — so it always suffices.

This one helper is deliberately *not* `private`, so that the proof file can
state the lemma the alternative rests on. -/
def filterDupsFuel [BEq α] : ℕ → List α → List α
  | 0, _ => []
  | _, [] => []
  | n + 1, a :: t => a :: filterDupsFuel n (t.filter (fun b => !(b == a)))

/-- Recursion that *filters* the tail with `!(b == a)` instead of erasing,
which is the equation `List.eraseDups_cons` states.  The head survives and every
later copy of it is filtered away. -/
def viaFilterDups [BEq α] (l : List α) : List α := filterDupsFuel l.length l

end Alt.List.eraseDups
