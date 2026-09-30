import Scripts.Test.Equiv.List.ZipWith

/-!
# Proofs: `List.zipWith` alternatives are equal to the original

All four alternatives in `../ZipWith.lean` are proved equal to `List.zipWith`
here.

Everything here is the mirror of `../Proofs/Zip.lean` with `f` applied, so the
structure — two degenerate cases first, then the lockstep step — is the same and
the proofs reuse the same lemma names.
-/

namespace Alt.List.zipWith

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-! ## `byRec` -/

theorem byRec_eq : ∀ (f : α → β → γ) (xs : List α) (ys : List β),
    byRec f xs ys = List.zipWith f xs ys
  | _, [], _ => rfl
  | _, _ :: _, [] => rfl
  | f, a :: t, b :: s => by simp [byRec, byRec_eq]

/-! ## `viaZipMap` -/

/-- The two-phase reading: build the alignment with `List.zip`, then decorate
it with `List.map`.  Mathlib has no lemma identifying this with `List.zipWith`,
so the identification is proved here by the same three-case induction as
`byRec`.  Mathlib's `List.countP_eq_length_filter` is the closest analogue for
this kind of "two phases, one pass each" identity. -/
private theorem zip_map_eq (f : α → β → γ) : ∀ (xs : List α) (ys : List β),
    List.map (fun p => f p.1 p.2) (List.zip xs ys) = List.zipWith f xs ys
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: t, b :: s => by simp [zip_map_eq]

theorem viaZipMap_eq (f : α → β → γ) (xs : List α) (ys : List β) :
    viaZipMap f xs ys = List.zipWith f xs ys := zip_map_eq f xs ys

/-! ## `byAccum` -/

/-- A tail-recursive loop with an explicit accumulator, consing `f a b` onto the
front as it is produced and reversing once at the end.  Same helper shape as
`byAccum` in `../Proofs/Zip.lean`, including the point that the accumulator is
reversed too, so the generalisation is

```
go f xs ys acc = acc.reverse ++ List.zipWith f xs ys
```

This definition has the same accumulator-inward shape as the *broken*
`Foldr.byTailLoop` (see `../Proofs/Foldr.lean`) and is nonetheless correct,
because of the final `reverse`.  Worth knowing that the two look alike. -/
theorem byAccum_eq (f : α → β → γ) (xs : List α) (ys : List β) :
    byAccum f xs ys = List.zipWith f xs ys := by
  have go : ∀ (xs : List α) (ys : List β) (acc : List γ),
      byAccum.go f xs ys acc = acc.reverse ++ List.zipWith f xs ys := by
    intro xs
    induction xs with
    | nil => intro ys acc; cases ys <;> rw [byAccum.go.eq_1] <;> simp
    | cons a t ih =>
      intro ys acc
      cases ys with
      | nil => rw [byAccum.go.eq_2 f (a :: t) acc (by simp)]; simp
      | cons b s => rw [byAccum.go.eq_def]; simp [ih]
  simp only [byAccum]
  rw [go]
  simp

/-! ## `byOfFn` -/

/-- The same three steps as `byOfFn` in `../Proofs/Zip.lean`: drop the bound
proofs with `List.get_eq_getElem`, bridge the two `Fin` indices with
`List.ofFn_congr` rather than `rw` (which fails, since `List.length_zipWith`
sits under a binder that a `getElem` proof depends on), and close pointwise with
`List.getElem_zipWith`.  Only the projections are different. -/
private theorem ofFn_eq_zipWith (f : α → β → γ) (xs : List α) (ys : List β) :
    List.ofFn (fun i : Fin (min xs.length ys.length) => f xs[↑i] ys[↑i])
      = List.zipWith f xs ys := by
  have hlen : (List.zipWith f xs ys).length = min xs.length ys.length := List.length_zipWith
  refine Eq.trans ?_ (List.ofFn_getElem (xs := List.zipWith f xs ys))
  refine Eq.trans ?_ (List.ofFn_congr hlen
    (fun i : Fin (List.zipWith f xs ys).length => (List.zipWith f xs ys)[↑i])).symm
  exact List.ofFn_inj.mpr (funext fun i =>
    (@List.getElem_zipWith _ _ _ f xs ys ↑i (hlen.symm ▸ i.isLt)).symm)

theorem byOfFn_eq (f : α → β → γ) (xs : List α) (ys : List β) :
    byOfFn f xs ys = List.zipWith f xs ys := by
  simp only [byOfFn, List.get_eq_getElem]
  exact ofFn_eq_zipWith f xs ys

/-! ## Against the original -/

theorem byRec_eq_orig (f : α → β → γ) (xs : List α) (ys : List β) :
    byRec f xs ys = orig f xs ys := byRec_eq f xs ys

theorem viaZipMap_eq_orig (f : α → β → γ) (xs : List α) (ys : List β) :
    viaZipMap f xs ys = orig f xs ys := viaZipMap_eq f xs ys

theorem byAccum_eq_orig (f : α → β → γ) (xs : List α) (ys : List β) :
    byAccum f xs ys = orig f xs ys := byAccum_eq f xs ys

theorem byOfFn_eq_orig (f : α → β → γ) (xs : List α) (ys : List β) :
    byOfFn f xs ys = orig f xs ys := byOfFn_eq f xs ys

end Alt.List.zipWith
