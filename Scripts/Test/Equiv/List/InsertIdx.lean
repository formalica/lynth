import Mathlib

/-!
# Alternative definitions: `List.insertIdx`

`List.insertIdx l i a` is `l` with `a` spliced in at position `i`.

**A trap worth recording.**  `List.insertIdx` is
`l.modifyTailIdx i (List.cons a)`, so an index *beyond* `l.length` is a
**no-op**, not an append, and the boundary is inclusive:

* `List.insertIdx [1, 2, 3] 3 0 = [1, 2, 3, 0]`, but
* `List.insertIdx [1, 2, 3] 4 0 = [1, 2, 3]`.

So the guard every route needs is `i ≤ l.length`, and even the empty list
inserts at `i = 0` (`List.insertIdx [] 0 a = [a]`) while ignoring `i = 3`.
Four routes:

* `viaTakeDrop` — cut the list at `i` with `take`/`drop` and splice, guarded on
  `i < l.length`;
* `byRec` — primitive recursion with the index as the recursion subject, written
  out, with the base case returning the list untouched;
* `byCounter` — count how many elements belong before the insertion point, then
  take that many and splice;
* `byFinRangeMap` — rebuild the whole list from its own indices, inserting the
  new element when the index hits `i` and shifting everything after it down one.

`byFinRangeMap` is the odd one out: it produces a list one position longer than
the input and reads the input at `j` and `j - 1`, so it is a genuine
index-shifting reconstruction rather than a splice.
-/

namespace Alt.List.insertIdx

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (l : List α) (i : ℕ) (a : α) : List α := List.insertIdx l i a

/-- Cut the list at `i` with `take` and `drop`, then splice the new element
between the halves.  The guard is needed: an out-of-range `i` leaves `l` alone
rather than appending. -/
def viaTakeDrop (l : List α) (i : ℕ) (a : α) : List α :=
  if i ≤ l.length then List.take i l ++ (a :: List.drop i l) else l

/-- Primitive recursion with the index as the recursion subject, written out.
Inserting at `0` conses, and inserting into `[]` at `i = 0` yields the singleton
`[a]` while any larger `i` yields the empty list, matching `modifyTailIdx`. -/
def byRec : List α → ℕ → α → List α
  | [], 0, a => [a]
  | [], _, _ => []
  | l, 0, a => a :: l
  | b :: t, n + 1, a => b :: byRec t n a

/-- Count how many elements belong before the insertion point — the number of
positions below `i` in `0 … l.length` — then take exactly that many and splice.
The index is consumed by a counter rather than by a recursion on `i`. -/
def byCounter (l : List α) (i : ℕ) (a : α) : List α :=
  let k := (List.range (l.length + 1)).takeWhile (fun j => j < i) |>.length
  if k < l.length + 1 then List.take k l ++ (a :: List.drop k l) else l

/-- Rebuild the whole list from its own indices.  The result is one position
longer than the input: at index `j < i` it reads `l[j]`, at `j = i` it returns the
new element, and after that it reads `l[j - 1]`, so the tail is shifted down one
position.  The `getD` fallback is never reached, and the whole reconstruction is
skipped for an out-of-range `i`. -/
def byFinRangeMap (l : List α) (i : ℕ) (a : α) : List α :=
  if i ≤ l.length then
    (List.finRange (l.length + 1)).map (fun j =>
      if j < i then l.getD j a else if j = i then a else l.getD (j - 1) a)
  else l

end Alt.List.insertIdx
