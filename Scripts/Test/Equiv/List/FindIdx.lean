import Mathlib

/-!
# Alternative definitions: `List.findIdx`

`List.findIdx p l` is the position of the first element satisfying `p`, and
`l.length` when there is none.  Four other routes:

* `byCounterRec` — primitive recursion returning the count of failing elements
  seen so far, written out rather than delegated to `List.findIdx`;
* `viaZipIdx` — tag every element with its index and search the *pairs*, so the
  search works on decorated data;
* `viaGetElemScan` — search the position list and fall back on `l.length`;
* `byFoldlCounter` — one left fold carrying an `Option`-valued latch for "not yet
  found" together with a position counter.

**A trap worth recording.**  The tempting fourth route — search the *reversed*
list and convert the distance from the end — does not work, and no arithmetic
saves it.  `findIdx` on the reversed list returns the **rightmost** match, and
looking for the first *failure* in the reversed scan only locates the leading run
of matches, not the last one: for `p = fun a => a % 5 < 2` on
`[0, 1, 2, 3, 4, 5, 6]` the reversed predicate values are `[T, T, F, F, F, T, T]`,
so the first failure sits at reversed position `2` while the leftmost match is at
index `0`.  The latch in `byFoldlCounter` scans forward instead.
-/

namespace Alt.List.findIdx

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig (p : α → Bool) (l : List α) : ℕ := List.findIdx p l

/-- Primitive recursion returning the count of failing elements so far, written
out. -/
def byCounterRec (p : α → Bool) : List α → ℕ
  | [] => 0
  | a :: t => if p a then 0 else byCounterRec p t + 1

/-- Tag every element with its index and search the *pairs*, so the search runs
on decorated data rather than on the elements themselves. -/
def viaZipIdx (p : α → Bool) (l : List α) : ℕ :=
  ((l.zipIdx).findIdx (fun pr => p pr.1))

/-- Search the position list, then read nothing: the answer is already the
index.  Falls back on `l.length` when nothing matches. -/
def viaGetElemScan (p : α → Bool) (l : List α) : ℕ :=
  (List.finRange l.length).findIdx? (fun i => p (l.get i)) |>.getD l.length

/-- A single left fold carrying an `Option` latch for "not yet found" and a
position counter.  The first success latches, and every later element is
skipped because the latch is already `some`; the result falls back on `l.length`
when the latch is never armed. -/
def byFoldlCounter (p : α → Bool) (l : List α) : ℕ :=
  ((List.foldl (fun (acc, k) a =>
      match acc with
      | some _ => (acc, k + 1)
      | none => if p a then (some k, k + 1) else (none, k + 1))
    (none, 0) l).1).getD l.length

end Alt.List.findIdx
