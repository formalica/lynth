import Mathlib

/-!
# Alternative definitions: `List.finRange`

`List.finRange n` is the list of the finite numbers below `n`.  Four other
routes:

* `byOfFnId` — the identity function on `Fin n`, enumerated;
* `byValWrap` — the index list mapped through the round trip `i ↦ ⟨i.val, i.isLt⟩`,
  so the bound is rebuilt from the value rather than the original `Fin n` being
  reused;
* `bySuccRec` — the successor equation written out: a fresh `0` followed by the
  old list shifted up by one.

The interesting contrast is `byOfFnId` against `List.finRange`: the latter is
*defined* as this, so the equality there is the definitional one, whereas
`byValWrap` goes the other way round and has to reattach the proofs.
-/

namespace Alt.List.finRange

/-- The original, kept as the reference point. -/
def orig (n : ℕ) : List (Fin n) := List.finRange n

/-- The identity function on `Fin n`, enumerated.  `List.ofFn` is the generic
"apply a function to every position" combinator. -/
def byOfFnId (n : ℕ) : List (Fin n) := List.ofFn (fun i => i)

/-- The index is projected to its value and the bound is rebuilt from it, rather
than the original `Fin n` being reused unchanged.  The position list is
`List.finRange`, so this differs from `byOfFnId` in the combinator rather than
in the function being enumerated. -/
def byValWrap (n : ℕ) : List (Fin n) :=
  (List.finRange n).map (fun i => ⟨i.val, i.isLt⟩)

/-- The successor equation, written out: one fresh `0`, then the list for `n`
shifted up by one with `Fin.succ`. -/
def bySuccRec : (n : ℕ) → List (Fin n)
  | 0 => []
  | n + 1 => ⟨0, Nat.succ_pos n⟩ :: (bySuccRec n).map Fin.succ

end Alt.List.finRange
