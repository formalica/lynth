import Mathlib

/-!
# Alternative definitions: `List.zipWith`

`List.zipWith` is `List.zip` with the pairing made into a binary function, so
the four alternatives below are the four ways one can decide *where* `f` gets
applied: fused into the recursion, applied after the fact, applied from an
index, or applied in a tail-recursive loop.

* `byRec` — structural recursion on both lists, `f` applied at each cons;
* `viaZipMap` — `List.zip` first, then `List.map` with a function that unpacks
  the pair and calls `f`.  The two-phase reading: build the alignment, then
  decorate it;
* `byOfFn` — index-driven over `Fin (min xs.length ys.length)`, reading both
  lists with `List.get`.  The truncation is decided once, by `min`, and `f` is
  applied to the two reads;
* `byAccum` — a `let rec` loop walking both lists together, consing `f a b`
  onto a reversed accumulator and reversing once at the end.

As in `AltListZip`, the elements of `xs` and `ys` are always consumed in
lockstep and in their original order; nothing is reordered.
-/

namespace Alt.List.zipWith

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- The original, kept as the reference point. -/
def orig (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  List.zipWith f xs ys

/-- Structural recursion on the pair of lists: `f` is applied to the two heads
and the result is consed onto the recursive tail. -/
def byRec (f : α → β → γ) : List α → List β → List γ
  | [], _ => []
  | _, [] => []
  | a :: t, b :: s => f a b :: byRec f t s

/-- The two-phase reading: first build the alignment with `List.zip`, then
decorate it with `List.map`.  `f` is applied only in the second pass, so the
intermediate list of pairs is materialised in full. -/
def viaZipMap (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  List.map (fun p => f p.1 p.2) (List.zip xs ys)

/-- Index-driven.  The number of output elements is `min xs.length ys.length`,
decided once up front; `List.ofFn` walks those positions and each step reads
both lists at index `i.val` before applying `f`. -/
def byOfFn (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  List.ofFn (fun i : Fin (min xs.length ys.length) =>
    f (xs.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_left xs.length ys.length)⟩)
      (ys.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.min_le_right xs.length ys.length)⟩))

/-- A tail-recursive walk with an explicit accumulator: cons `f a b` onto the
front as it is produced and reverse once at the end.  Every recursive call is
in tail position, and the termination condition (either list exhausted) is
checked in one place. -/
def byAccum (f : α → β → γ) (xs : List α) (ys : List β) : List γ :=
  let rec go : List α → List β → List γ → List γ
    | [], _, acc => acc.reverse
    | _, [], acc => acc.reverse
    | a :: t, b :: s, acc => go t s (f a b :: acc)
  go xs ys []

end Alt.List.zipWith
