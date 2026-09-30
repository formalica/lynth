import Mathlib

/-!
# Alternative definitions: `List.drop`

`List.drop n l` is `l` with the first `n` elements removed.  Four other routes:

* `byRec` — primitive recursion on the count, written out;
* `byIterTail` — apply `List.tail` once per element of `List.range n`, so the
  skipping is an iteration rather than a recursion on `n`;
* `byGetElemMap` — enumerate the positions that *survive* and read each one,
  rebuilding the list from its own indices;
* `byCounter` — a single left fold carrying a position counter, discarding
  while the counter is below `n` and consing afterwards.

`byIterTail` is the notable one: it never inspects the structure of `l` during
the recursion, it just asks for `n` tails in a row.
-/

namespace Alt.List.drop

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (n : ℕ) (l : List α) : List α := List.drop n l

/-- Primitive recursion on the count, written out rather than delegated to
`List.drop`. -/
def byRec : ℕ → List α → List α
  | 0, l => l
  | _ + 1, [] => []
  | n + 1, _ :: t => byRec n t

/-- Apply `List.tail` once per element of `List.range n`.  The recursion never
looks at `l`: it just requests `n` tails in succession, and on `[]` `tail` is
absent so nothing happens. -/
def byIterTail (n : ℕ) (l : List α) : List α :=
  (List.range n).foldl (fun l _ => List.tail l) l

/-- Enumerate the positions that survive — `n, …, length - 1` — and read each
one, rebuilding the list out of its own indices.  The index into the position
list is *offset* by `n`, so the position list runs from `0` and the reads start
at `n`. -/
def byGetElemMap (n : ℕ) (l : List α) : List α :=
  (List.finRange (l.length - n)).map (fun i => l.get ⟨n + i.val, by omega⟩)

/-- A single left fold that carries a position counter: discard while the
counter is below `n`, then keep everything.  The kept elements are consed onto
the front, so one `reverse` restores their order. -/
def byCounter (n : ℕ) (l : List α) : List α :=
  ((List.foldl (fun (acc, k) a =>
      if k < n then (acc, k + 1) else (a :: acc, k))
    ([], 0) l).1).reverse

end Alt.List.drop
