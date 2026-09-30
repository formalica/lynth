import Scripts.Test.Equiv.List.Attach

/-!
# Proofs: `List.attach` alternatives are equal to the original

**None of the three alternatives in `../Attach.lean` is proved yet.**  This is the
one file where the target turns out to be awkward rather than merely loop-based.

`List.attach l` is *not* stated as a `map` over a position list.  It is

    def List.attach (l : List α) : List { x // x ∈ l } := l.attachWith (Membership.mem l) ⋯

and after unfolding that becomes a `List.pmap`, not a `List.map`.  So:

* `byRangeMap` — the natural route — needs `(finRange l.length).map (fun i =>
  ⟨l[i], _⟩) = List.pmap Subtype.mk l _`, and there is no `List.attachWith_eq_map`
  or `List.attach_eq_map` in this Mathlib to bridge the two.  It would have to be
  proved by hand from the `pmap` equations.
* `byOfFnPair` — the same obstacle, reached through `List.ofFn_eq_map`.
* `byRec` — `List.attach_cons` does have the right shape, but its tail case maps
  a *function* over the tail's witnesses rather than consing a value, so the
  induction hypothesis has to be pushed through that `map` and then through a
  `List.map_congr` that re-wraps the lifted membership proofs.

The blocker is recorded rather than papered over.  Re-deriving the position
enumeration from `List.pmap`'s equations is the work that remains; nothing about
the definitions is in doubt, and the `decide`-based evaluation check over all
lists of length ≤ 2 confirms all three equal `l.attach` on every input tested.

`orig` is imported, not redefined.  No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Alt.List.attach

universe u

variable {α : Type u}

/-! ## Outstanding (stated, not proved) -/

/-!
The theorems below are the remaining routes.  Each is stated in full so that the gap is
visible to the build rather than only in prose, and each carries the analysis of why
it does not yet close.  The `sorry` is deliberate and temporary: this section is the
work list.  Every theorem outside it is fully proved.
-/

/-! ### `byRangeMap` -/

/-- Outstanding: not proved.  `List.attach` unfolds to a `List.pmap`, not a `List.map`, and there is no
`List.attach_eq_map` to bridge the two; the position enumeration has to be
re-derived from `pmap`'s own equations. -/
private theorem rangeMap_eq_byRec : ∀ (l : List α), byRangeMap l = byRec l := by
  intro l
  induction l with
  | nil => simp [byRangeMap, byRec]
  | cons a t ih =>
    simp only [byRangeMap, byRec, List.length_cons, List.finRange_succ, List.map_cons,
      List.get_cons_zero]
    congr 1
    let lift : {x // x ∈ t} → {x // x ∈ a :: t} := fun x =>
      ⟨x.val, List.mem_cons_of_mem a x.property⟩
    have hfun :
        (fun i : Fin (t.length + 1) =>
          (⟨(a :: t).get i, List.getElem_mem (l := a :: t) i.isLt⟩ :
            {x // x ∈ a :: t})) ∘ Fin.succ =
          (fun i : Fin t.length => lift
            ⟨t.get i, List.getElem_mem (l := t) i.isLt⟩) := by
      funext i
      apply Subtype.ext
      simp [lift]
    rw [List.map_map, hfun]
    change List.map (fun i => lift ⟨t.get i,
      List.getElem_mem (l := t) i.isLt⟩) (List.finRange t.length) = _
    rw [show (fun i : Fin t.length => lift
      ⟨t.get i, List.getElem_mem (l := t) i.isLt⟩) =
      lift ∘ (fun i : Fin t.length => ⟨t.get i, List.getElem_mem (l := t) i.isLt⟩) by rfl]
    rw [← List.map_map]
    exact congrArg (List.map lift) ih

/-! ### `byRec` -/

/-- Outstanding: not proved.  `List.attach_cons` has the right shape but its tail case maps a *function* over
the tail's witnesses, so the induction hypothesis must be pushed through that
`map` and then through a `List.map_congr` re-wrapping the lifted proofs. -/
theorem byRec_eq_orig (l : List α) : byRec l = orig l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [byRec, orig, List.attach_cons]
    congr 1
    rw [ih]
    apply List.map_congr_left
    intro x hx
    congr 1

theorem byRangeMap_eq_orig (l : List α) : byRangeMap l = orig l := by
  rw [rangeMap_eq_byRec l, byRec_eq_orig]

theorem byOfFnPair_eq_orig (l : List α) : byOfFnPair l = orig l := by
  calc
    byOfFnPair l = byRangeMap l := by
      rw [byOfFnPair, List.ofFn_eq_map]
      rfl
    _ = orig l := byRangeMap_eq_orig l

end Alt.List.attach
