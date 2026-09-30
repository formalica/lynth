import Scripts.Test.Equiv.Nat.Div

/-!
# Proofs: `Nat.div` alternatives are equal to the original

All four alternatives in `../Div.lean` are proved equal to `a / b` here.

`bySub` carries a `termination_by` and decreases the *first* argument, so it needs
strong induction on `a` with `b` generalised; the one arithmetic step it needs
(`a / b = (a - b) / b + 1`) is `Nat.mul_add_div` with `b ≤ a`.

The two counting schemes are proved through the characterisation
`j + 1 ≤ a / b ↔ (j + 1) * b ≤ a` (`Nat.le_div_iff_mul_le`): the fold keeps
`min (a / b) (k + 1)`, and the count accumulates the indicator that each
successor index is a multiple of `b`.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.div

private theorem div_sub_add (a b : ℕ) (hb : 0 < b) (h : b ≤ a) :
    a / b = (a - b) / b + 1 := by
  have h1 := Nat.mul_add_div hb 1 (a - b)
  rw [Nat.mul_one, Nat.add_sub_of_le h] at h1
  omega

theorem bySub_eq (a b : ℕ) : bySub a b = a / b := by
  induction a using Nat.strong_induction_on generalizing b with
  | h a ih => cases b with
    | zero => rw [bySub, Nat.div_zero]
    | succ n =>
      rw [bySub]
      by_cases hc : a < n + 1
      · rw [ite_eq_left hc, Nat.div_eq_of_lt hc]
      · rw [ite_eq_right (by omega)]
        rw [ih (a - (n + 1)) (by omega) (n + 1)]
        exact (div_sub_add a (n + 1) (by omega) (by omega)).symm

/-- After visiting `k` the sweep holds `min (a / b) (k + 1)`: the step takes `k + 1`
whenever that is still within the quotient, and otherwise leaves the old value. -/
private theorem foldl_max (a b : ℕ) (hb : 0 < b) : ∀ (k : ℕ),
    (List.range (k + 1)).foldl (fun acc j => if (j + 1) * b ≤ a then j + 1 else acc) 0
      = min (a / b) (k + 1) := by
  intro k
  have key : ∀ (j : ℕ), j + 1 ≤ a / b ↔ (j + 1) * b ≤ a :=
    fun j => (Nat.le_div_iff_mul_le hb)
  induction k with
  | zero =>
    rw [List.range_succ, List.foldl_append, List.range_zero, List.foldl_nil,
      List.foldl_cons, List.foldl_nil]
    by_cases h : b ≤ a
    · have h1 : 0 + 1 ≤ a / b := (key 0).mpr (by omega)
      rw [ite_eq_left ((key 0).mp h1), Nat.min_eq_right h1]
    · have h1 : a / b = 0 := Nat.div_eq_of_lt (by omega)
      have h2 : 0 ≤ 0 + 1 := by omega
      have hne : ¬((0 + 1) * b ≤ a) := fun hh => h (by
        have hq := (key 0).mpr hh
        have h2' := (key 0).mp hq
        omega)
      rw [ite_eq_right hne, h1, Nat.min_eq_left h2]
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, ih, List.foldl_cons, List.foldl_nil]
    by_cases h1 : m + 1 + 1 ≤ a / b
    · rw [ite_eq_left ((key (m + 1)).mp h1), Nat.min_eq_right h1]
    · have h2 : a / b ≤ m + 1 := by omega
      have h3 : a / b ≤ m + 1 + 1 := by omega
      have h4 : ¬((m + 1 + 1) * b ≤ a) := fun hh => h1 ((key (m + 1)).mpr hh)
      rw [ite_eq_right h4, Nat.min_eq_left h2, Nat.min_eq_left h3]

theorem viaRangeFold_eq (a b : ℕ) : viaRangeFold a b = a / b := by
  rw [viaRangeFold]
  by_cases h : b = 0
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    rw [foldl_max a b (by omega) a]
    have hd := Nat.div_le_self a b
    have hle : a / b ≤ a + 1 := by omega
    rw [Nat.min_eq_left hle]

/-- The positive multiples of `b` in `[0, n]` are exactly `b, 2b, …, (n / b) * b`,
so their number is `n / b`; `Nat.succ_div` is the step. -/
private theorem countP_mult (b : ℕ) : ∀ (n : ℕ), 0 < b →
    (List.range (n + 1)).countP (fun k => k != 0 && k % b == 0) = n / b := by
  intro n hb
  induction n with
  | zero =>
    have hnil : List.countP (fun k => k != 0 && k % b == 0) [] = 0 := rfl
    have h0 : ((0 : ℕ) != 0 && 0 % b == 0) = false := by simp
    have hr : List.range (0 + 1) = [0] := by simp [List.range_succ]
    rw [hr, List.countP_cons, hnil, h0, ite_eq_right (by decide), Nat.zero_div]
  | succ m ih =>
    have hnil : List.countP (fun k => k != 0 && k % b == 0) [] = 0 := rfl
    have hr : List.range (m + 1 + 1) = List.range (m + 1) ++ [m + 1] := by
      simp [List.range_succ]
    rw [hr, List.countP_append, ih, List.countP_cons, hnil, Nat.zero_add]
    rw [Nat.succ_div]
    have hp : ((m + 1) != 0 && (m + 1) % b == 0) = decide (b ∣ m + 1) := by
      simp [Nat.dvd_iff_mod_eq_zero]
      rfl
    rw [hp]
    by_cases hb2 : b ∣ m + 1
    · simp [hb2]
    · simp [hb2]

theorem viaRangeCount_eq (a b : ℕ) : viaRangeCount a b = a / b := by
  rw [viaRangeCount]
  by_cases h : b = 0
  · rw [ite_eq_left h]
    simp [h]
  · rw [ite_eq_right h]
    exact countP_mult b a (by omega)

theorem viaFilterLength_eq (a b : ℕ) : viaFilterLength a b = a / b := by
  rw [viaFilterLength, ← List.countP_eq_length_filter]
  exact viaRangeCount_eq a b

/-! ## Against the original -/

theorem bySub_eq_orig (a b : ℕ) : bySub a b = orig a b := bySub_eq a b

theorem viaRangeFold_eq_orig (a b : ℕ) : viaRangeFold a b = orig a b := viaRangeFold_eq a b

theorem viaRangeCount_eq_orig (a b : ℕ) : viaRangeCount a b = orig a b := viaRangeCount_eq a b

theorem viaFilterLength_eq_orig (a b : ℕ) : viaFilterLength a b = orig a b :=
  viaFilterLength_eq a b

end Alt.Nat.div
