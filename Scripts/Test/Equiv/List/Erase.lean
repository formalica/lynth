import Mathlib

/-!
# Alternative definitions: `List.erase`

`List.erase l a` is `l` with its **first** element equal to `a` removed.  Four
other routes:

* `byRec` — primitive recursion with the test written as `if b == a then`;
* `viaTakeDrop` — locate the position with `findIdx`, then cut at it;
* `viaEraseIdx` — locate the position and hand it to `List.eraseIdx`, which is a
  positional (rather than a value-based) deletion;
* `byFoldlLatch` — a left fold carrying a "a copy has already been dropped"
latch: the first match is dropped and the latch is armed, and every later element
is kept.  The survivors are consed onto the front, so one `reverse` restores
their order.

The `[BEq α]` instance is used only through `==`, and "first" is taken in the
sense of that test: with a `BEq` that is not lawful, `a ∈ l` in the propositional
sense and `a == b` can disagree, so none of the routes below may be phrased in
terms of `∈`.
-/

namespace Alt.List.erase

universe u

variable {α : Type u}

/-- The original, kept as the reference point. -/
def orig [BEq α] (l : List α) (a : α) : List α := l.erase a

/-- Primitive recursion with the test written as `if b == a then`. -/
def byRec [BEq α] : List α → α → List α
  | [], _ => []
  | b :: t, a => if b == a then t else b :: byRec t a

/-- Locate the position with `findIdx` and then cut the list at it.  When the
element is absent the index is `l.length` and the guard falls back on `l` itself. -/
def viaTakeDrop [BEq α] (l : List α) (a : α) : List α :=
  let i := l.findIdx (fun b => b == a)
  if i < l.length then List.take i l ++ List.drop (i + 1) l else l

/-- Locate the position and hand it to `List.eraseIdx`, which deletes *by
index* rather than by value — a positional deletion dressed up as a search. -/
def viaEraseIdx [BEq α] (l : List α) (a : α) : List α :=
  l.eraseIdx (l.findIdx (fun b => b == a))

/-- A single left fold with a latch.  The first element that matches is dropped
and the latch is armed; every later element is consed, including later copies of
the same value, so exactly one occurrence goes.  The survivors are consed onto
the front, so one `reverse` restores their order. -/
def byFoldlLatch [BEq α] (l : List α) (a : α) : List α :=
  ((List.foldl (fun (acc, dropped) b =>
      if b == a && !dropped then (acc, true) else (b :: acc, dropped))
    ([], false) l).1).reverse

end Alt.List.erase
