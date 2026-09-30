import Scripts.Test.Equiv.Nat.Lcm

/-!
# Proofs: `Nat.lcm` alternatives are equal to the original

All four definitions are proved.  The three search-based ones share a block of
private machinery about ascending lists: in an ascending list of naturals the
first qualifying element is the one `find?` returns, and a `foldl` that freezes
on the first non-zero accumulator agrees with it.

The key arithmetic input is the characterisation `Nat.lcm a b ≤ a * b` together
with "every positive common multiple is a multiple of the lcm", which is what
makes the lcm the *least* positive common multiple and hence the head of the
filtered range.

`orig` is imported, not redefined.  No `sorry`, no `axiom`.
-/

namespace Alt.Nat.lcm

/-! ## `viaGcdProduct` -/

/-- Inverting `lcm a b * gcd a b = a * b`.  The zero cases have to be split off
first: `lcm 0 b = 0` and the gcd is then `b > 0`, so the quotient would be
meaningless. -/
theorem viaGcdProduct_eq (a b : ℕ) : viaGcdProduct a b = Nat.lcm a b := by
  by_cases h0 : a = 0 ∨ b = 0
  · rw [viaGcdProduct, ite_eq_left h0]
    rcases h0 with ha | hb
    · rw [ha, Nat.lcm_zero_left]
    · rw [hb, Nat.lcm_zero_right]
  · rw [viaGcdProduct, ite_eq_right h0]
    have ha : a ≠ 0 := fun e => h0 (Or.inl e)
    have hpa : 0 < a := Nat.pos_of_ne_zero ha
    have hg := Nat.gcd_pos_of_pos_left b hpa
    have hrec := Nat.lcm_mul_gcd a b
    rw [← hrec, Nat.mul_comm, Nat.mul_div_cancel_left (Nat.lcm a b) hg]

theorem viaGcdProduct_eq_orig (a b : ℕ) : viaGcdProduct a b = orig a b :=
  viaGcdProduct_eq a b

/-! ## Machinery for the three searches over a bounded range -/

private theorem btrue_ite {x y : ℕ} {c : Bool} (hc : c = true) : (if c then x else y) = x :=
  ite_eq_left hc

private theorem bfalse_ite {x y : ℕ} {c : Bool} (hc : ¬ c = true) : (if c then x else y) = y :=
  ite_eq_right hc

private theorem cm_spec (a b m : ℕ) :
    (m != 0 && m % a == 0 && m % b == 0) = true ↔ 0 < m ∧ a ∣ m ∧ b ∣ m := by
  simp [Nat.dvd_iff_mod_eq_zero, Nat.pos_iff_ne_zero, and_assoc]

private theorem q_spec (b m : ℕ) :
    (m != 0 && m % b == 0) = true ↔ 0 < m ∧ b ∣ m := by
  simp [Nat.dvd_iff_mod_eq_zero, Nat.pos_iff_ne_zero]

private theorem range_asc : ∀ (n : ℕ), (List.range n).Pairwise (· ≤ ·) := by
  intro n
  induction n with
  | zero => rw [List.range_zero]; exact List.Pairwise.nil
  | succ k ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
    intro x hx y hy
    simp only [List.mem_singleton] at hy
    have hxk : x < k := List.mem_range.mp hx
    omega

private theorem map_mul_asc (a n : ℕ) :
    ((List.range n).map (fun k => k * a)).Pairwise (· ≤ ·) :=
  List.Pairwise.map _ (fun _ _ h => Nat.mul_le_mul_right a h) (range_asc n)

/-- `a * b` is a common multiple, so it bounds the lcm. -/
private theorem lcm_le_mul (a b : ℕ) (hpa : 0 < a) (hpb : 0 < b) :
    Nat.lcm a b ≤ a * b := by
  have hd : Nat.lcm a b ∣ a * b :=
    Nat.lcm_dvd (Nat.dvd_mul_right a b) (Nat.dvd_mul_left b a)
  exact Nat.le_of_dvd (Nat.mul_pos hpa hpb) hd

/-- Every positive common multiple is at least the lcm. -/
private theorem lcm_least (a b m : ℕ) (hm : 0 < m) (h1 : a ∣ m) (h2 : b ∣ m) :
    Nat.lcm a b ≤ m :=
  Nat.le_of_dvd (by omega) (Nat.lcm_dvd h1 h2)

private theorem lcm_div_le (a b : ℕ) (hpa : 0 < a) (hpb : 0 < b) :
    Nat.lcm a b / a ≤ b := by
  have hle := lcm_le_mul a b hpa hpb
  have hid : a * (Nat.lcm a b / a) = Nat.lcm a b :=
    Nat.mul_div_cancel' (Nat.dvd_lcm_left a b)
  have hmul : a * (Nat.lcm a b / a) ≤ a * b := by omega
  exact Nat.le_of_mul_le_mul_left hmul hpa

/-- In an ascending list, the first qualifying element is the one `find?`
returns. -/
private theorem find?_first : ∀ (L : List ℕ) (P : ℕ → Bool), L.Pairwise (· ≤ ·) →
    ∀ (m : ℕ), P m = true → m ∈ L → (∀ d ∈ L, d < m → P d = false) →
      L.find? P = some m := by
  intro L P h
  induction L with
  | nil => intro m hPm hm hlt; exact absurd hm (by simp)
  | cons e L ih =>
    intro m hPm hm hlt
    have hL : L.Pairwise (· ≤ ·) := (List.pairwise_cons.mp h).2
    rw [List.find?_cons]
    cases hbe : P e with
    | true =>
      change some e = some m
      have h1 : m ≤ e := by
        by_contra hc
        have hl := hlt e List.mem_cons_self (Nat.lt_of_not_ge hc)
        rw [hl] at hbe
        exact Bool.noConfusion hbe
      rcases List.mem_cons.mp hm with hme | hmL
      · exact congrArg some hme.symm
      · have hem : e = m := by
          have h2 : e ≤ m := List.rel_of_pairwise_cons h hmL
          omega
        exact congrArg some hem
    | false =>
      change List.find? P L = some m
      have hmL : m ∈ L := by
        rcases List.mem_cons.mp hm with h | h
        · rw [h] at hPm
          rw [hPm] at hbe
          exact Bool.noConfusion hbe
        · exact h
      refine ih hL m hPm hmL ?_
      intro d hd hdm
      exact hlt d (List.mem_cons_of_mem e hd) hdm

private theorem step_zero (P : ℕ → Bool) (x : ℕ) (hx : P x = true) :
    (if (0 : ℕ) != 0 then (0 : ℕ) else if P x then x else 0) = x := by
  rw [bfalse_ite (by simp), btrue_ite hx]

private theorem foldl_stuck (P : ℕ → Bool) (acc : ℕ) (hacc : acc ≠ 0) :
    ∀ (L : List ℕ),
      L.foldl (fun acc x => if acc != 0 then acc else if P x then x else 0) acc = acc := by
  intro L
  induction L with
  | nil => rfl
  | cons e L ih =>
    rw [List.foldl_cons, btrue_ite (by simp [hacc]), ih]

/-- A `foldl` that latches onto the first non-zero accumulator visits an
ascending list in order, so it agrees with `find?`. -/
private theorem foldl_first : ∀ (L : List ℕ) (P : ℕ → Bool), L.Pairwise (· ≤ ·) →
    ∀ (m : ℕ), m ≠ 0 → P m = true → m ∈ L → (∀ d ∈ L, d < m → P d = false) →
      L.foldl (fun acc x => if acc != 0 then acc else if P x then x else 0) 0 = m := by
  intro L P h
  induction L with
  | nil => intro m hm0 hPm hm hlt; exact absurd hm (by simp)
  | cons e L ih =>
    intro m hm0 hPm hm hlt
    have hL : L.Pairwise (· ≤ ·) := (List.pairwise_cons.mp h).2
    rw [List.foldl_cons]
    by_cases hmL : m ∈ L
    · by_cases he : P e = true
      · have h1 : m ≤ e := by
          by_contra hc
          have hl := hlt e List.mem_cons_self (Nat.lt_of_not_ge hc)
          rw [hl] at he
          exact Bool.noConfusion he
        have h2 : e ≤ m := List.rel_of_pairwise_cons h hmL
        have hstep : (if (0 : ℕ) != 0 then (0 : ℕ) else if P e then e else 0) = m :=
          (step_zero P e he).trans (by omega)
        rw [hstep, foldl_stuck P m hm0 L]
      · have hz : (if (0 : ℕ) != 0 then (0 : ℕ) else if P e then e else 0) = 0 :=
          (bfalse_ite (by simp)).trans (bfalse_ite he)
        rw [hz]
        refine ih hL m hm0 hPm hmL ?_
        intro d hd hdm
        exact hlt d (List.mem_cons_of_mem e hd) hdm
    · have hme : m = e := by
        rcases List.mem_cons.mp hm with h | h
        · exact h
        · exact absurd h hmL
      rw [hme] at hPm
      have hstep : (if (0 : ℕ) != 0 then (0 : ℕ) else if P e then e else 0) = m :=
        (step_zero P e hPm).trans hme.symm
      rw [hstep, foldl_stuck P m hm0 L]

/-! ## `viaHeadOfCommonMultiples` -/

theorem viaHeadOfCommonMultiples_eq (a b : ℕ) :
    viaHeadOfCommonMultiples a b = Nat.lcm a b := by
  by_cases h0 : a = 0 ∨ b = 0
  · rw [viaHeadOfCommonMultiples, ite_eq_left h0]
    rcases h0 with ha | hb
    · rw [ha, Nat.lcm_zero_left]
    · rw [hb, Nat.lcm_zero_right]
  · have hpa : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (Or.inl e))
    have hpb : 0 < b := Nat.pos_of_ne_zero (fun e => h0 (Or.inr e))
    have hlm := Nat.lcm_pos hpa hpb
    have hle := lcm_le_mul a b hpa hpb
    have hmem : ((List.range (a * b + 1)).filter
        (fun m => m != 0 && m % a == 0 && m % b == 0)).head? = some (Nat.lcm a b) := by
      rw [List.head?_filter]
      refine find?_first _ _ (range_asc _) _ ?_ ?_ ?_
      · exact (cm_spec a b _).mpr ⟨hlm, Nat.dvd_lcm_left a b, Nat.dvd_lcm_right a b⟩
      · exact List.mem_range.mpr (by omega)
      · intro d hd hdl
        cases hP : (d != 0 && d % a == 0 && d % b == 0) with
        | true =>
          obtain ⟨hdm, h1, h2⟩ := (cm_spec a b d).mp hP
          have hle := lcm_least a b d hdm h1 h2
          omega
        | false => rfl
    rw [viaHeadOfCommonMultiples, ite_eq_right h0, hmem]
    rfl

theorem viaHeadOfCommonMultiples_eq_orig (a b : ℕ) :
    viaHeadOfCommonMultiples a b = orig a b := viaHeadOfCommonMultiples_eq a b

/-! ## `viaFoldFirstCommon` -/

theorem viaFoldFirstCommon_eq (a b : ℕ) :
    viaFoldFirstCommon a b = Nat.lcm a b := by
  by_cases h0 : a = 0 ∨ b = 0
  · rw [viaFoldFirstCommon, ite_eq_left h0]
    rcases h0 with ha | hb
    · rw [ha, Nat.lcm_zero_left]
    · rw [hb, Nat.lcm_zero_right]
  · have hpa : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (Or.inl e))
    have hpb : 0 < b := Nat.pos_of_ne_zero (fun e => h0 (Or.inr e))
    have hlm := Nat.lcm_pos hpa hpb
    have hle := lcm_le_mul a b hpa hpb
    have hmem : (List.range (a * b + 1)).foldl (fun acc m =>
        if acc != 0 then acc
        else if m != 0 && m % a == 0 && m % b == 0 then m else 0) 0 = Nat.lcm a b := by
      refine foldl_first _ _ (range_asc _) _ ?_ ?_ ?_ ?_
      · exact Nat.pos_iff_ne_zero.mp hlm
      · exact (cm_spec a b _).mpr ⟨hlm, Nat.dvd_lcm_left a b, Nat.dvd_lcm_right a b⟩
      · exact List.mem_range.mpr (by omega)
      · intro d hd hdl
        cases hP : (d != 0 && d % a == 0 && d % b == 0) with
        | true =>
          obtain ⟨hdm, h1, h2⟩ := (cm_spec a b d).mp hP
          have hle := lcm_least a b d hdm h1 h2
          omega
        | false => rfl
    rw [viaFoldFirstCommon, ite_eq_right h0, hmem]

theorem viaFoldFirstCommon_eq_orig (a b : ℕ) :
    viaFoldFirstCommon a b = orig a b := viaFoldFirstCommon_eq a b

/-! ## `viaRangeScan` -/

theorem viaRangeScan_eq (a b : ℕ) : viaRangeScan a b = Nat.lcm a b := by
  by_cases h0 : a = 0 ∨ b = 0
  · rw [viaRangeScan, ite_eq_left h0]
    rcases h0 with ha | hb
    · rw [ha, Nat.lcm_zero_left]
    · rw [hb, Nat.lcm_zero_right]
  · have hpa : 0 < a := Nat.pos_of_ne_zero (fun e => h0 (Or.inl e))
    have hpb : 0 < b := Nat.pos_of_ne_zero (fun e => h0 (Or.inr e))
    have hlm := Nat.lcm_pos hpa hpb
    have hle := lcm_le_mul a b hpa hpb
    have hdiv := lcm_div_le a b hpa hpb
    have hmem : (((List.range (b + 1)).map (fun k => k * a)).filter
        (fun m => m != 0 && m % b == 0)).head? = some (Nat.lcm a b) := by
      rw [List.head?_filter]
      refine find?_first _ _ (map_mul_asc a (b + 1)) _ ?_ ?_ ?_
      · exact (q_spec b _).mpr ⟨hlm, Nat.dvd_lcm_right a b⟩
      · refine List.mem_map.mpr ⟨Nat.lcm a b / a, List.mem_range.mpr (by omega), ?_⟩
        rw [Nat.mul_comm]
        exact Nat.mul_div_cancel' (Nat.dvd_lcm_left a b)
      · intro d hd hdl
        cases hP : (d != 0 && d % b == 0) with
        | true =>
          obtain ⟨hdm, h2⟩ := (q_spec b d).mp hP
          obtain ⟨k, hk, he⟩ := List.mem_map.mp hd
          have hda : a ∣ d := by rw [← he]; exact Nat.dvd_mul_left a k
          have hle := lcm_least a b d hdm hda h2
          omega
        | false => rfl
    rw [viaRangeScan, ite_eq_right h0]
    change (((List.range (b + 1)).map (fun k => k * a)).filter
      (fun m => m != 0 && m % b == 0)).head?.getD 0 = Nat.lcm a b
    rw [hmem]
    rfl

theorem viaRangeScan_eq_orig (a b : ℕ) : viaRangeScan a b = orig a b := viaRangeScan_eq a b

end Alt.Nat.lcm
