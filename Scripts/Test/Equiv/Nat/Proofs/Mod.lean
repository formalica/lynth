import Scripts.Test.Equiv.Nat.Mod

/-!
# Proofs: `Nat.mod` alternatives are equal to the original

All five alternatives in `../Mod.lean` are proved equal to `a % b` here.

`bySub` and `bySteps` carry a `termination_by` and decrease the *first* argument,
so both need strong induction on `a` with `b` generalised — a plain induction on
`b` never produces the recursive call.  `viaRangeFold` needs the same shape plus
the observation that each step of the sweep strictly decreases the accumulator,
so the sweep reaches its fixed point within `a` steps.

`viaRangeSaturate` is a character-for-character copy of `viaRangeFold`, so its
theorem is a one-liner.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.mod

theorem bySub_eq (a b : ℕ) : bySub a b = a % b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih => cases b with
    | zero => rw [bySub, Nat.mod_zero]
    | succ n =>
      rw [bySub]
      by_cases hc : a < n + 1
      · rw [ite_eq_left hc, Nat.mod_eq_of_lt hc]
      · rw [ite_eq_right (by omega)]
        rw [ih (a - (n + 1)) (by omega) (n + 1)]
        exact (Nat.mod_eq_sub_mod (Nat.le_of_not_gt hc)).symm

theorem viaDiv_eq (a b : ℕ) : viaDiv a b = a % b := by
  rw [viaDiv]
  by_cases h : b = 0
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h, Nat.mul_comm (a / b) b]
    have hd := Nat.mod_add_div a b
    omega

private theorem go_mod (b : ℕ) : ∀ (x : ℕ), bySteps.go x b = x % b := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    cases b with
    | zero => rw [bySteps.go, Nat.mod_zero]
    | succ n =>
      rw [bySteps.go]
      by_cases hc : x < n + 1
      · rw [ite_eq_left hc, Nat.mod_eq_of_lt hc]
      · rw [ite_eq_right (by omega)]
        rw [ih (x - (n + 1)) (by omega)]
        exact (Nat.mod_eq_sub_mod (Nat.le_of_not_gt hc)).symm

theorem bySteps_eq (a b : ℕ) : bySteps a b = a % b := by
  rw [bySteps]
  exact go_mod b a

/-- The sweep subtracts `b` until the running value is below `b`, and then stops
moving.  `b ≠ 0` is assumed because with `b = 0` the step is the identity and
nothing decreases. -/
private theorem foldl_step (b : ℕ) (hb : b ≠ 0) : ∀ (x : ℕ), ∀ (xs : List ℕ),
    xs.length ≥ x → xs.foldl (fun y _ => if y < b then y else y - b) x = x % b := by
  intro x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro xs hx
    by_cases hxb : x < b
    · have hid : ∀ (zs : List ℕ),
          zs.foldl (fun y _ => if y < b then y else y - b) x = x := by
        intro zs
        induction zs with
        | nil => rfl
        | cons u t iht => rw [List.foldl_cons, ite_eq_left hxb, iht]
      rw [hid, Nat.mod_eq_of_lt hxb]
    · cases xs with
      | nil =>
        simp only [List.length_nil] at hx
        have h0 : x = 0 := by omega
        rw [h0, Nat.zero_mod]
        rfl
      | cons u t =>
        rw [List.foldl_cons, ite_eq_right hxb]
        simp only [List.length_cons] at hx
        have hb1 : 1 ≤ b := by omega
        have hlt : x - b < x := by omega
        have hle : t.length ≥ x - b := by omega
        rw [ih (x - b) hlt t hle]
        exact (Nat.mod_eq_sub_mod (Nat.le_of_not_gt hxb)).symm

theorem viaRangeFold_eq (a b : ℕ) : viaRangeFold a b = a % b := by
  rw [viaRangeFold]
  by_cases h : b = 0
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    exact foldl_step b h a (List.range a) (by rw [List.length_range])

theorem viaRangeSaturate_eq (a b : ℕ) : viaRangeSaturate a b = a % b :=
  viaRangeFold_eq a b

/-! ## Against the original -/

theorem bySub_eq_orig (a b : ℕ) : bySub a b = orig a b := bySub_eq a b

theorem bySteps_eq_orig (a b : ℕ) : bySteps a b = orig a b := bySteps_eq a b

theorem viaDiv_eq_orig (a b : ℕ) : viaDiv a b = orig a b := viaDiv_eq a b

theorem viaRangeFold_eq_orig (a b : ℕ) : viaRangeFold a b = orig a b := viaRangeFold_eq a b

theorem viaRangeSaturate_eq_orig (a b : ℕ) : viaRangeSaturate a b = orig a b :=
  viaRangeSaturate_eq a b

end Alt.Nat.mod
