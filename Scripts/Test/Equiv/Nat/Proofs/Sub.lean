import Scripts.Test.Equiv.Nat.Sub

/-!
# Proofs: `Nat.sub` alternatives are equal to the original

All five alternatives in `../Sub.lean` are proved equal to `a - b` here.

`recOnSecond`, `recBoth` and `plain` carry a `termination_by` and so are
well-founded recursions: `rfl` and `simp [def]` cannot reduce them, only the
equation lemmas used with `rw` can.  The two arithmetic-free schemes need the
counter lemmas: `viaMin` clamps first, `viaAddCount` scans upward, and both
reduce to the same two facts about `viaAddCount.go` — that the scan returns
`a - b` once the counter is inside the window, and that it returns `0` once the
counter is past it.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.sub

theorem recOnSecond_eq (a b : ℕ) : recOnSecond a b = a - b := by
  induction b with
  | zero => rw [recOnSecond, Nat.sub_zero]
  | succ n ih => rw [recOnSecond, ih]; omega

theorem plain_eq (a b : ℕ) : plain a b = a - b := by
  induction b with
  | zero => rw [plain, Nat.sub_zero]
  | succ n ih => rw [plain, ih]; omega

theorem recBoth_eq (a b : ℕ) : recBoth a b = a - b := by
  induction a generalizing b with
  | zero => cases b with
    | zero => rw [recBoth]
    | succ n => rw [recBoth, Nat.zero_sub]
  | succ m ih => cases b with
    | zero => rw [recBoth, Nat.sub_zero]; simp
    | succ n => rw [recBoth, ih n]; omega

theorem viaMin_eq (a b : ℕ) : viaMin a b = a - b := by
  rw [viaMin, plain_eq]
  by_cases h : a ≤ b
  · rw [Nat.min_eq_left h, Nat.sub_self, Nat.sub_eq_zero_of_le h]
  · rw [Nat.min_eq_right (Nat.le_of_not_ge h)]

/-- With `b ≤ a` the equation `c + b = a` has the unique solution `c = a - b`,
so once the counter is inside `[c, c + fuel]` the scan must return it.  The two
boundary cases are forced: with no fuel left the counter is already the answer,
and with `c = a - b` the guard is already satisfied. -/
private theorem go_count (a b : ℕ) (h : b ≤ a) : ∀ (fuel c : ℕ), c ≤ a - b →
    a - b ≤ c + fuel → viaAddCount.go a b c fuel = a - b := by
  intro fuel
  induction fuel with
  | zero =>
    intro c h1 h2
    have h3 : c = a - b := by omega
    subst h3
    rw [viaAddCount.go, ite_eq_left (by omega)]
  | succ f ih =>
    intro c h1 h2
    by_cases hc : c = a - b
    · rw [hc, viaAddCount.go, ite_eq_left (by omega)]
    · rw [viaAddCount.go, ite_eq_right (by omega : ¬(c + b = a))]
      exact ih (c + 1) (by omega) (by omega)

/-- Past `a - b` the counter can never satisfy `c + b = a`, so the scan always
falls through to `0`.  This is what covers `b > a`, where the answer is `0`. -/
private theorem go_past (a b : ℕ) : ∀ (fuel c : ℕ), a - b < c →
    viaAddCount.go a b c fuel = 0 := by
  intro fuel
  induction fuel with
  | zero =>
    intro c hc
    rw [viaAddCount.go, ite_eq_right (by omega : ¬(c + b = a))]
  | succ f ih =>
    intro c hc
    rw [viaAddCount.go, ite_eq_right (by omega : ¬(c + b = a))]
    exact ih (c + 1) (by omega)

theorem viaAddCount_eq (a b : ℕ) : viaAddCount a b = a - b := by
  rw [viaAddCount]
  by_cases hb : b ≤ a
  · exact go_count a b hb a 0 (Nat.zero_le _) (by omega)
  · by_cases ha : a = 0
    · rw [ha, viaAddCount.go]
      split <;> omega
    · obtain ⟨a', ha'⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
      rw [ha', viaAddCount.go, ite_eq_right (by omega : ¬(0 + b = a' + 1)),
        Nat.zero_add, go_past (a' + 1) b a' 1 (by omega)]
      omega

/-! ## Against the original -/

theorem recOnSecond_eq_orig (a b : ℕ) : recOnSecond a b = orig a b := recOnSecond_eq a b

theorem recBoth_eq_orig (a b : ℕ) : recBoth a b = orig a b := recBoth_eq a b

theorem plain_eq_orig (a b : ℕ) : plain a b = orig a b := plain_eq a b

theorem viaMin_eq_orig (a b : ℕ) : viaMin a b = orig a b := viaMin_eq a b

theorem viaAddCount_eq_orig (a b : ℕ) : viaAddCount a b = orig a b := viaAddCount_eq a b

end Alt.Nat.sub
