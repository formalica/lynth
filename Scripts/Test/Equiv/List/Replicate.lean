import Mathlib

/-!
# Alternative definitions: `List.replicate`

`List.replicate n a` is `a` repeated `n` times.  Four other routes:

* `byOfFn` — a constant function on `Fin n`, enumerated;
* `byRangeMap` — `List.range n` mapped through a constant, i.e. the list of
  positions turned into the list of copies;
* `byFoldlRev` — a left fold that conses and is then reversed, so the copy is
  made by accumulation rather than by recursion;
* `bySuccRec` — primitive recursion on the count.

The four differ in the combinator used (`ofFn`, `map`, `foldl` + `reverse`,
direct recursion) but agree on the triviality of the element being copied, which
is the point: the count is the only thing that varies.
-/

namespace Alt.List.replicate

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (n : ℕ) (a : α) : List α := List.replicate n a

/-- A constant function on `Fin n`, enumerated.  `List.ofFn` is the generic
"apply a function to every position" combinator; the function ignores its input
and returns `a`. -/
def byOfFn (n : ℕ) (a : α) : List α := List.ofFn (fun _ : Fin n => a)

/-- `List.range n` mapped through a constant: the list of positions is turned
into the list of copies.  This is the general "`n` copies of a pattern" shape,
and `List.range` supplies the positions. -/
def byRangeMap (n : ℕ) (a : α) : List α := (List.range n).map (fun _ => a)

/-- A left fold that conses the copy onto the front of the accumulator, finished
by one `reverse`.  Copies are made by accumulation, not by recursion on the
count, so the shape of the computation is a loop rather than a descent. -/
def byFoldlRev (n : ℕ) (a : α) : List α :=
  (List.range n).foldl (fun acc _ => a :: acc) ([] : List α) |>.reverse

/-- Primitive recursion on the count, written out. -/
def bySuccRec : ℕ → α → List α
  | 0, _ => []
  | n + 1, a => a :: bySuccRec n a

end Alt.List.replicate
