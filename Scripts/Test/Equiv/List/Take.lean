import Mathlib

/-!
# Alternative definitions: `List.take`

`List.take n l` is the first `n` elements, or all of `l` if it is shorter.  Four
other routes:

* `byRec` — primitive recursion on the count, written out;
* `viaRevDropRev` — the complement: drop from the *reversed* list the
  `length - n` elements that lie past the cutoff and reverse back, leaving
  exactly the first `n`;
* `byGetElemMap` — enumerate the positions that survive and read each one, so
  the list is rebuilt from its own indices;
* `byCounter` — a single left fold carrying a position counter, appending while
  the counter is still below `n` and skipping afterwards.

`byCounter` and `byGetElemMap` are both index-driven but differ in whether the
indices come from a separate position list or are threaded through the fold. -/

namespace Alt.List.take

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (n : ℕ) (l : List α) : List α := List.take n l

/-- Primitive recursion on the count, written out rather than delegated to
`List.take`. -/
def byRec : ℕ → List α → List α
  | 0, _ => []
  | _ + 1, [] => []
  | n + 1, a :: t => a :: byRec n t

/-- The complement, taken from the wrong end first: drop the `length - n`
elements that lie past the cutoff *of the reversed list* and reverse back, which
leaves exactly the first `n`.  Dropping from the front of `l` itself would give
the last `n` instead, which is the trap here. -/
def viaRevDropRev (n : ℕ) (l : List α) : List α :=
  (l.reverse.drop (l.length - n)).reverse

/-- Enumerate the positions that survive — `0, …, min n l.length - 1` — and read
each one, rebuilding the list out of its own indices.  The bound of the position
list is the *minimum*, so `List.get` needs the index re-wrapped rather than a
fallback. -/
def byGetElemMap (n : ℕ) (l : List α) : List α :=
  (List.finRange (min n l.length)).map (fun i => l.get ⟨i.val, by omega⟩)

/-- A single left fold that carries a position counter: keep appending while the
counter is below `n`, then ignore everything after.  No recursion on `n`, and no
separate position list. -/
def byCounter (n : ℕ) (l : List α) : List α :=
  (List.foldl (fun (acc, k) a =>
      if k < n then (acc ++ [a], k + 1) else (acc, k))
    ([], 0) l).1

end Alt.List.take
