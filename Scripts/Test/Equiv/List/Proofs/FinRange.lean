import Scripts.Test.Equiv.List.FinRange

/-!
# Proofs: `List.finRange` alternatives are equal to the original

All three alternatives in `../FinRange.lean` are proved equal to `List.finRange`
here.  `byOfFnId` is free — `List.ofFn_id` says exactly that `List.finRange` *is*
the enumeration of the identity, which is worth recording because it means the
equality there is the definitional one.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.finRange

/-! ## `byOfFnId` -/

/-- `List.ofFn_id` is the statement: `List.finRange` is *defined* as the
enumeration of the identity on `Fin n`. -/
theorem byOfFnId_eq_finRange (n : ℕ) : byOfFnId n = List.finRange n :=
  List.ofFn_id n

/-! ## `byValWrap` -/

/-- The round trip `i ↦ ⟨i.val, i.isLt⟩` *is* the identity, and the `Fin` bound
proofs are irrelevant, so re-wrapping the values gives the identity enumeration
back. -/
private theorem val_wrap_id (n : ℕ) :
    (fun i : Fin n => ⟨i.val, i.isLt⟩) = (fun i : Fin n => i) := by
  funext i
  rfl

theorem byValWrap_eq_finRange (n : ℕ) : byValWrap n = List.finRange n := by
  rw [byValWrap, ← List.ofFn_id n, List.map_ofFn]
  have h : (fun i : Fin n => ⟨i.val, i.isLt⟩) ∘ id = fun i : Fin n => i := by
    funext i
    rfl
  rw [h]
  rfl

/-! ## `bySuccRec` -/

/-- The successor equation written out by hand.  The fresh `⟨0, Nat.succ_pos n⟩`
and the `0` that `List.finRange_succ` produces are the same `Fin (n + 1)`: the
bound is a `Prop` and so proof irrelevance makes the two pairs equal. -/
theorem bySuccRec_eq_finRange : ∀ (n : ℕ), bySuccRec n = List.finRange n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [bySuccRec, List.finRange_succ, ih]
    congr 1

/-! ## Against the original -/

theorem byOfFnId_eq_orig (n : ℕ) : byOfFnId n = orig n := byOfFnId_eq_finRange n

theorem byValWrap_eq_orig (n : ℕ) : byValWrap n = orig n := byValWrap_eq_finRange n

theorem bySuccRec_eq_orig (n : ℕ) : bySuccRec n = orig n := bySuccRec_eq_finRange n

end Alt.List.finRange
