import Mathlib

/-!
# Alternative definitions: `List.span`

`List.span p l` cuts `l` after its longest *prefix* satisfying `p` and returns
both parts.  Three other routes:

* `viaTakeWhileDropWhile` — the obvious decomposition into two independent
  functions, each of which scans the list from the front;
* `bySharedWhileRec` — a single structural recursion producing both parts,
  where the loop is written out explicitly with cons rather than delegated to
  `takeWhile`/`dropWhile`;
* `byCounter` — one left fold carrying a Boolean "still in the prefix" flag and
  both halves, so the cut is a two-state machine inside the fold.

Note the asymmetry with `splitAt`: here the split point is not known in advance
but *decided* by the predicate, which is why the state machine in `byCounter`
has to carry a flag rather than a counter.
-/

namespace Alt.List.span

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (p : α → Bool) (l : List α) : List α × List α := List.span p l

/-- The obvious decomposition: the prefix is what `takeWhile` accepts and the
rest is what `dropWhile` rejects. -/
def viaTakeWhileDropWhile (p : α → Bool) (l : List α) : List α × List α :=
  (List.takeWhile p l, List.dropWhile p l)

/-- A single structural recursion producing both parts, with the loop written
out rather than delegated to `takeWhile`/`dropWhile`. -/
def bySharedWhileRec (p : α → Bool) : List α → List α × List α
  | [] => ([], [])
  | a :: t =>
    if p a then let (x, y) := bySharedWhileRec p t; (a :: x, y) else ([], a :: t)

/-- One left fold carrying a Boolean "still in the prefix" flag and both halves.
Once the flag is cleared it never returns, which is what makes the cut
monotone. -/
def byCounter (p : α → Bool) (l : List α) : List α × List α :=
  let r := List.foldl (fun (pre, post, inPre) a =>
      if inPre ∧ p a then (pre ++ [a], post, true)
      else (pre, a :: post, false))
    (([], [], true) : List α × List α × Bool) l
  (r.1, r.2.1.reverse)

end Alt.List.span
