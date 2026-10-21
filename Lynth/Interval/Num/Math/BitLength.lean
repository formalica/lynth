import Mathlib.Data.Nat.Log

/-! Portable equality used only to select a faster native implementation.
The bounded binary search remains the kernel implementation. -/

namespace Lynth.Interval.Vendor.Dyadic

def bitSearchS (n : Nat) : Nat → Nat → Nat → Nat
  | 0, _, hi => hi
  | fuel + 1, lo, hi =>
    cond (hi.ble (lo + 1)) hi
      (cond ((n >>> ((lo + hi) / 2)).beq 0) (bitSearchS n fuel lo ((lo + hi) / 2))
        (bitSearchS n fuel ((lo + hi) / 2) hi))

/-- The search has enough iterations for either initial bracket. The upper
cap is intentional: preserve the original behavior even above 65536 bits. -/
theorem bitSearchS_eq_log2 (n : Nat) (hn : n ≠ 0) :
    bitSearchS n 20 0 (cond ((n >>> 256).beq 0) 256 65536) =
      min 65536 (n.log2 + 1) := by
  have half_size (lo hi C : Nat) (h : hi - lo ≤ C * 2) :
    ((lo + hi) / 2) - lo ≤ C ∧ hi - ((lo + hi) / 2) ≤ C  := by
    omega
  have ble_false_lt {x y : Nat} (h : x.ble y = false) : y < x  := by
    by_contra hh
    have hle : x ≤ y := Nat.not_lt.mp hh
    have h2 : x.ble y = true := Nat.ble_eq_true_of_le hle
    simp [h] at h2
  have shiftRight_eq_zero_log2 {n : Nat} (hn : n ≠ 0) (k : Nat) :
    n >>> k = 0 ↔ n.log2 < k  := by
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff, Nat.log2_lt hn]
    exact or_iff_right (Nat.two_pow_pos k).ne'
  have bitSearchS_cap (n hi₀ : Nat) (hn : n ≠ 0) (hA : hi₀ ≤ n.log2 + 1) :
    ∀ fuel lo hi, hi - lo ≤ 2 ^ fuel → lo < hi₀ → hi = hi₀ →
      bitSearchS n fuel lo hi = hi₀  := by
    intro fuel
    induction fuel with
    | zero =>
      intro lo hi _ hlo hhi
      simp only [bitSearchS]
      exact hhi
    | succ fuel ih =>
      intro lo hi hsize hlo hhi
      rw [Nat.pow_succ] at hsize
      simp only [bitSearchS]
      cases hb : hi.ble (lo + 1)
      · -- `false`: `lo + 1 < hi`, bisect
        have hgt : lo + 1 < hi := ble_false_lt hb
        have hge : lo + 2 ≤ hi := by omega
        simp only [Bool.cond_false]
        cases h2 : (n >>> ((lo + hi) / 2)).beq 0
        · -- `false`: recurse right; the bracket shrinks, the top is unchanged
          simp only [Bool.cond_false]
          have hmid : (lo + hi) / 2 ≤ hi - 1 := by omega
          have hm1 : (lo + hi) / 2 < hi₀ := by omega
          have hstep := half_size lo hi (2 ^ fuel) hsize
          exact ih ((lo + hi) / 2) hi hstep.2 hm1 hhi
        · -- `true`: recurse left; impossible in the capped case
          simp only [Bool.cond_true]
          have hm1 : n.log2 < (lo + hi) / 2 :=
            (shiftRight_eq_zero_log2 hn _).mp (by simpa using h2)
          have hmid : (lo + hi) / 2 ≤ hi - 1 := by omega
          have hcontr : False := by omega
          exact hcontr.elim
      · -- `true`: `hi ≤ lo + 1`, the bracket is already collapsed
        have hle : hi ≤ lo + 1 := Nat.le_of_ble_eq_true hb
        simp only [Bool.cond_true]
        exact hhi
  have bitSearchS_uncap (n : Nat) (_hn : n ≠ 0)
    (hsh : ∀ k : Nat, n >>> k = 0 ↔ n.log2 < k) :
    ∀ fuel lo hi, hi - lo ≤ 2 ^ fuel → lo < n.log2 + 1 → n.log2 + 1 ≤ hi →
      bitSearchS n fuel lo hi = n.log2 + 1  := by
    intro fuel
    induction fuel with
    | zero =>
      intro lo hi hsize hlo hhi
      have hsize : hi - lo ≤ 1 := by simpa using hsize
      simp only [bitSearchS]
      omega
    | succ fuel ih =>
      intro lo hi hsize hlo hhi
      rw [Nat.pow_succ] at hsize
      simp only [bitSearchS]
      cases hb : hi.ble (lo + 1)
      · -- `false`: `lo + 1 < hi`, bisect
        have hgt : lo + 1 < hi := ble_false_lt hb
        have hge : lo + 2 ≤ hi := by omega
        simp only [Bool.cond_false]
        cases h2 : (n >>> ((lo + hi) / 2)).beq 0
        · -- `false`: recurse right
          simp only [Bool.cond_false]
          have hne : ¬ (n >>> ((lo + hi) / 2) = 0) := by
            intro h0
            simp [h0] at h2
          have hm1 : (lo + hi) / 2 < n.log2 + 1 := by
            have hle : (lo + hi) / 2 ≤ n.log2 :=
              Nat.le_of_not_lt (mt (hsh _).mpr hne)
            omega
          have hstep := half_size lo hi (2 ^ fuel) hsize
          exact ih ((lo + hi) / 2) hi hstep.2 hm1 hhi
        · -- `true`: recurse left
          simp only [Bool.cond_true]
          have hm1 : n.log2 < (lo + hi) / 2 :=
            (hsh _).mp (by simpa using h2)
          have hm2 : n.log2 + 1 ≤ (lo + hi) / 2 := by omega
          have hstep := half_size lo hi (2 ^ fuel) hsize
          exact ih lo ((lo + hi) / 2) hstep.1 hlo hm2
      · -- `true`: `hi ≤ lo + 1`, the bracket has collapsed onto the target
        have hle : hi ≤ lo + 1 := Nat.le_of_ble_eq_true hb
        simp only [Bool.cond_true]
        omega

  have hsh : ∀ k : Nat, n >>> k = 0 ↔ n.log2 < k := shiftRight_eq_zero_log2 hn
  have hsz : ∀ m : Nat, m ≤ 65536 → m - 0 ≤ 2 ^ 20 := by
    intro m hm
    have hle : m - 0 ≤ 65536 := by omega
    exact le_trans hle (by decide)
  cases h : (n >>> 256).beq 0
  · -- `false`: the initial bracket reaches 65536
    simp only [Bool.cond_false]
    refine (le_total (n.log2 + 1) 65536).elim ?_ ?_
    · intro hM
      rw [min_eq_right hM]
      exact bitSearchS_uncap n hn hsh 20 0 65536 (hsz _ le_rfl) (by omega) hM
    · intro hM
      rw [min_eq_left hM]
      exact bitSearchS_cap n 65536 hn hM 20 0 65536 (hsz _ le_rfl) (by decide) rfl
  · -- `true`: the bracket is capped at 256, so necessarily n.log2 < 256
    simp only [Bool.cond_true]
    have h0 : n >>> 256 = 0 := by simpa using h
    have hM : n.log2 + 1 ≤ 256 := by
      have := (hsh 256).mp h0
      omega
    rw [min_eq_right (by omega : n.log2 + 1 ≤ 65536)]
    exact bitSearchS_uncap n hn hsh 20 0 256 (hsz _ (by omega)) (by omega) hM
end Lynth.Interval.Vendor.Dyadic
