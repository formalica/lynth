import Mathlib

/-!
# Alternative definitions: `List.splitAt`

`List.splitAt n l` cuts `l` after `n` elements and returns both halves.  Three
other routes:

* `viaTakeDrop` — the obvious decomposition into two independent functions;
* `bySharedRec` — a single structural recursion that produces both halves at
  once, carrying the split point in the recursion rather than computing the
  pieces separately;
* `byCounter` — one left fold carrying a position counter and both halves, so
  the cut is a state machine inside the fold rather than a recursion on `n`.

`bySharedRec` and `viaTakeDrop` compute the same information; the difference is
that the first makes a single pass and the second makes two.
-/

namespace Alt.List.splitAt

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (n : ℕ) (l : List α) : List α × List α := List.splitAt n l

/-- The obvious decomposition: the first half is what `take` returns and the
second is what `drop` returns. -/
def viaTakeDrop (n : ℕ) (l : List α) : List α × List α :=
  (List.take n l, List.drop n l)

/-- A single structural recursion producing both halves together, so the two
pieces are built in one pass and never computed separately. -/
def bySharedRec : ℕ → List α → List α × List α
  | 0, l => ([], l)
  | _ + 1, [] => ([], [])
  | n + 1, a :: t => let (x, y) := bySharedRec n t; (a :: x, y)

/-- One left fold carrying a position counter and both halves: elements go to
the left half while the counter is below `n`, and to the right half afterwards.
The cut is a state machine inside the fold rather than a recursion on `n`. -/
def byCounter (n : ℕ) (l : List α) : List α × List α :=
  let r := List.foldl (fun (pre, post, k) a =>
      if k < n then (pre ++ [a], post, k + 1) else (pre, a :: post, k))
    (([], [], 0) : List α × List α × ℕ) l
  (r.1, r.2.1.reverse)

end Alt.List.splitAt
