import Mathlib

/-!
# Alternative definitions: `List.reverse`

Six ways to turn a list around.  `List.reverse` is one accumulator recursion
(cons onto an accumulator while walking the list), so the alternatives here
deliberately vary the *scheme*, not just the combinator: a `foldl` cons,
a naive quadratic `++ [x]` recursion, a `foldr` that appends, a positional
rewrite driven by `List.range` and `getElem?`, and a "peel the last element,
repeat" loop built from `getLast?`/`dropLast`.

The trap for this function is asymmetry: `reverse` must be an involution, and
`[].reverse = []`.  The tempting recursion `reverse (x :: xs) = x :: reverse xs`
is the *identity*, not the reverse.  Every definition below was checked against
the original on all lists of length ≤ 3 over `{0, 1}`, where that mistake shows
up immediately.
-/

namespace Alt.List.reverse

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) : List α := List.reverse l

/-- The accumulator recursion spelled out, with the accumulator as the second
argument so the recursion is visibly on the list.  This is the shape
`List.reverse` itself uses. -/
def withAcc (l : List α) (acc : List α) : List α :=
  match l with
  | [] => acc
  | x :: t => withAcc t (x :: acc)

/-- `withAcc` started from the empty accumulator, i.e. the plain reversal. -/
def direct (l : List α) : List α := withAcc l []

/-- Reversal by `foldl`: cons each element onto the front of the accumulator.
A different combinator for the same accumulator idea, and unlike `withAcc` the
library drives the recursion. -/
def viaFoldl (l : List α) : List α := l.foldl (fun acc x => x :: acc) []

/-- The naive quadratic recursion: reverse the tail, then append the head at
the *end*.  Correct, and much slower than the linear versions. -/
def viaAppend (l : List α) : List α :=
  match l with
  | [] => []
  | x :: t => (viaAppend t) ++ [x]

/-- `foldr` that appends instead of consing.  `foldr` hands the accumulator of
the *tail* to the head, so `acc ++ [x]` puts the head last: a reversal, reached
from the opposite end of the list relative to `viaFoldl`. -/
def viaFoldrAppend (l : List α) : List α := l.foldr (fun x acc => acc ++ [x]) []

/-- Positional rewrite, step 1: for each index `i` of `List.range l.length`,
emit the *mirror* index `l.length - 1 - i` as a `getElem?` probe.  Because
`foldr` builds the list from the right, the probes come out in the order
`n-1, …, 0` — but as `Option`s, so the step is total. -/
def viaIndexScan (l : List α) : List (Option α) :=
  (List.range l.length).foldr (fun i acc => l[l.length - 1 - i]? :: acc) []

/-- Positional rewrite, step 2: drop the `none`s.  All probes are in range by
construction, so this is the reversed list.  No recursion on the list at all —
indexing, not consing. -/
def viaIndex (l : List α) : List α := (viaIndexScan l).filterMap id

/-- "Peel the last element off, repeat": a `getLast?`-driven loop, decreasing
on an explicit `ℕ` fuel rather than on the list, so no termination proof about
`dropLast` is needed. -/
def viaPeel : ℕ → List α → List α → List α
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | n + 1, l, acc =>
      match l.getLast? with
      | none => acc
      | some x => viaPeel n l.dropLast (acc ++ [x])

/-- `viaPeel` with fuel `l.length` and an empty accumulator. -/
def viaDrop (l : List α) : List α := viaPeel l.length l []

end Alt.List.reverse
