import Scripts.Test.Equiv.Nat.Gcd

/-!
# Proofs: `Nat.gcd` alternatives are equal to the original

All six definitions are proved.  The three list-driven ones share a block of
private machinery about ascending lists: in an ascending list of naturals the
last element is the maximum, and both a `foldl` that keeps the most recent
qualifier and a `foldr` that latches onto the first non-zero accumulator land
on that maximum.

The `orig` and `commonDivisors` are imported, not redefined.  No `sorry`, no
axiom.
-/

namespace Alt.Nat.gcd

/-! ## `euclid` -/

/-- The Euclidean recursion.  `euclid a b` recurses on the pair `(b, a % b)`,
whose second component is *strictly* smaller — so it is strong induction on the
second argument, not ordinary induction.  The gcd is invariant under
`Nat.gcd_rec`. -/
theorem euclid_eq (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
    by_cases hb : b = 0
    · rw [hb, euclid, ite_eq_left (by omega), Nat.gcd_zero_right]
    · rw [euclid, ite_eq_right hb]
      rw [ih (a % b) (Nat.mod_lt _ (Nat.pos_of_ne_zero hb)) b]
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a]
      exact Nat.gcd_comm _ _

theorem euclid_eq_orig (a b : ℕ) : euclid a b = orig a b := euclid_eq a b

/-! ## `commonDivisors` -/

/-- The common divisors of `a` and `b` in `[0, min a b]`, ascending.  This is
the shared building block; its *content* is what matters, and it says exactly
"the common divisors of `a` and `b` bounded by `min a b`". -/
theorem commonDivisors_spec (a b d : ℕ) :
    d ∈ commonDivisors a b ↔ d ≤ min a b ∧ d ∣ a ∧ d ∣ b := by
  simp only [commonDivisors, List.mem_filter, List.mem_range, Bool.and_eq_true,
    decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, Nat.dvd_of_mod_eq_zero h2, Nat.dvd_of_mod_eq_zero h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨by omega, ⟨Nat.dvd_iff_mod_eq_zero.mp h2, Nat.dvd_iff_mod_eq_zero.mp h3⟩⟩

/-! ## Machinery for the three scans over `commonDivisors` -/

private theorem ite0 (c : Bool) : (if c then (0 : ℕ) else 0) = 0 := by
  cases c <;> rfl

private theorem cand_true (a b d : ℕ) :
    ((a % d = 0) && (b % d = 0)) = true ↔ a % d = 0 ∧ b % d = 0 := by
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- A positive common divisor is bounded by the gcd. -/
private theorem dvd_le_gcd (a b d : ℕ) (hg : 0 < Nat.gcd a b) (h1 : a % d = 0)
    (h2 : b % d = 0) : d ≤ Nat.gcd a b := by
  rcases Nat.eq_zero_or_pos d with rfl | hpos
  · omega
  · exact Nat.le_of_dvd hg (Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2))

private theorem getLast_mem' : ∀ (L : List ℕ) (w : ℕ), L.getLast? = some w → w ∈ L := by
  intro L w h
  by_cases hne : L = []
  · rw [hne] at h
    simp at h
  · have hwe : w = L.getLast hne :=
      Option.some.inj (h.symm.trans (List.getLast?_eq_getLast_of_ne_nil hne))
    rw [hwe]; exact List.getLast_mem hne

/-- `List.range n` is ascending. -/
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

/-- In an ascending list of naturals, an element dominating all the others is
the last one. -/
private theorem asc_max : ∀ (L : List ℕ), L.Pairwise (· ≤ ·) →
    ∀ (g : ℕ), g ∈ L → (∀ d ∈ L, d ≤ g) → L.getLast? = some g := by
  intro L
  induction L with
  | nil => intro h g hg hall; exact absurd hg (by simp)
  | cons e L ih =>
    intro h g hg hall
    have hL : L.Pairwise (· ≤ ·) := (List.pairwise_cons.mp h).2
    have hcross : ∀ x ∈ L, e ≤ x := fun x hx => List.rel_of_pairwise_cons h hx
    rw [List.getLast?_cons]
    simp only [Option.some.injEq]
    rcases List.mem_cons.mp hg with hge | hgL
    · cases hl : L.getLast? with
      | none => rw [Option.getD_none]; exact hge.symm
      | some w =>
        have hwmem : w ∈ L := getLast_mem' L w hl
        have h1 : w ≤ g := hall w (List.mem_cons_of_mem e hwmem)
        have h2 : e ≤ w := hcross w hwmem
        rw [Option.getD_some]
        omega
    · rw [ih hL g hgL (fun d hd => hall d (List.mem_cons_of_mem e hd))]
      rw [Option.getD_some]

/-- A `foldr` that latches onto the first non-zero accumulator, evaluated on a
list whose last element is a positive `g`, returns `g`. -/
private theorem foldr_latch : ∀ (L : List ℕ) (g : ℕ), 0 < g → L.getLast? = some g →
    L.foldr (fun d acc => if acc = 0 then d else acc) 0 = g := by
  intro L
  induction L with
  | nil => intro g hgpos hg; simp at hg
  | cons e L ih =>
    intro g hgpos hg
    rw [List.getLast?_cons] at hg
    simp only [Option.some.injEq] at hg
    rw [List.foldr_cons]
    cases hl : L.getLast? with
    | none =>
      have hLe : L = [] := List.getLast?_eq_none_iff.mp hl
      have hge : L.getLast?.getD e = e := by rw [hLe]; rfl
      have hgg : e = g := hge.symm.trans hg
      rw [hLe, List.foldr_nil]
      by_cases hc : (0 : ℕ) = 0
      · rw [ite_eq_left hc]; exact hgg
      · rw [ite_eq_right hc]; exact absurd rfl hc
    | some w =>
      simp only [hl, Option.getD_some] at hg
      have hwpos : 0 < w := by omega
      rw [ih w hwpos hl, ite_eq_right (by omega : ¬(w = 0))]
      exact hg

private theorem commonDivisors_asc (a b : ℕ) : (commonDivisors a b).Pairwise (· ≤ ·) := by
  rw [commonDivisors]
  exact List.Pairwise.filter _ (range_asc _)

private theorem gcd_mem_commonDivisors (a b : ℕ) (hpa : 0 < a) (hpb : 0 < b) :
    Nat.gcd a b ∈ commonDivisors a b := by
  rw [commonDivisors_spec]
  have hgd := Nat.gcd_dvd a b
  exact ⟨le_min (Nat.gcd_le_left b hpa) (Nat.gcd_le_right a hpb), hgd.1, hgd.2⟩

private theorem commonDivisors_le_gcd (a b : ℕ) (hg : 0 < Nat.gcd a b) :
    ∀ d ∈ commonDivisors a b, d ≤ Nat.gcd a b := by
  intro d hd
  rw [commonDivisors_spec] at hd
  exact dvd_le_gcd a b d hg (Nat.dvd_iff_mod_eq_zero.mp hd.2.1)
    (Nat.dvd_iff_mod_eq_zero.mp hd.2.2)

/-- The gcd is the last common divisor in the ascending candidate list. -/
private theorem commonDivisors_last (a b : ℕ) (hpa : 0 < a) (hpb : 0 < b) :
    (commonDivisors a b).getLast? = some (Nat.gcd a b) :=
  asc_max (commonDivisors a b) (commonDivisors_asc a b) _
    (gcd_mem_commonDivisors a b hpa hpb)
    (commonDivisors_le_gcd a b (Nat.gcd_pos_of_pos_left b hpa))

/-! ## `byScan` -/

/-- Induction on the size of the scanned range.  The fold only ever reaches a
common divisor `g ≤ m`, and once the range has reached `g` the answer is `g`. -/
private theorem foldl_gcd (a b : ℕ) (g : ℕ) (hgd : g ∣ a ∧ g ∣ b) :
    ∀ (m : ℕ), g ≤ m →
      (∀ d, d ≤ m → (a % d = 0) → (b % d = 0) → d ≤ g) →
      (List.range (m + 1)).foldl
          (fun acc d => if (a % d = 0) && (b % d = 0) then d else acc) 0 = g := by
  intro m
  induction m with
  | zero =>
    intro hm hb
    rw [List.range_succ, List.range_zero, List.foldl_append, List.foldl_nil,
      List.foldl_cons, ite0, List.foldl_nil]
    omega
  | succ n ih =>
    intro hm hb
    have hr : List.range (n + 1 + 1) = List.range (n + 1) ++ [n + 1] := by
      simp [List.range_succ]
    by_cases hg1 : g ≤ n
    · rw [hr, List.foldl_append, List.foldl_cons]
      have hfold : (List.range (n + 1)).foldl
          (fun acc d => if (a % d = 0) && (b % d = 0) then d else acc) 0 = g :=
        ih hg1 (fun d hd h1 h2 => hb d (by omega) h1 h2)
      rw [hfold, List.foldl_nil]
      by_cases hq : ((a % (n + 1) = 0) && (b % (n + 1) = 0)) = true
      · rw [ite_eq_left hq]
        obtain ⟨h1, h2⟩ := cand_true a b (n + 1) |>.mp hq
        have := hb (n + 1) (by omega) h1 h2
        omega
      · rw [ite_eq_right hq]
    · rw [hr, List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hgm : n + 1 = g := by omega
      have hdm : n + 1 ∣ a := by rw [hgm]; exact hgd.1
      have hdm2 : n + 1 ∣ b := by rw [hgm]; exact hgd.2
      have hpos1 : a % (n + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdm
      have hpos2 : b % (n + 1) = 0 := Nat.dvd_iff_mod_eq_zero.mp hdm2
      rw [ite_eq_left (cand_true a b (n + 1) |>.mpr ⟨hpos1, hpos2⟩)]
      exact hgm

theorem byScan_eq (a b : ℕ) : byScan a b = Nat.gcd a b := by
  by_cases ha : a = 0
  · simp [byScan, ha, Nat.gcd_zero_left]
  by_cases hb : b = 0
  · simp [byScan, ha, hb, Nat.gcd_zero_right]
  have hpa : 0 < a := Nat.pos_of_ne_zero ha
  have hpb : 0 < b := Nat.pos_of_ne_zero hb
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b hpa
  rw [byScan, ite_eq_right ha, ite_eq_right hb]
  exact foldl_gcd a b (Nat.gcd a b) (Nat.gcd_dvd a b) (min a b)
    (le_min (Nat.gcd_le_left b hpa) (Nat.gcd_le_right a hpb))
    (fun d _ h1 h2 => dvd_le_gcd a b d hg h1 h2)

theorem byScan_eq_orig (a b : ℕ) : byScan a b = orig a b := byScan_eq a b

/-! ## `byFind` -/

theorem byFind_eq (a b : ℕ) : byFind a b = Nat.gcd a b := by
  by_cases ha : a = 0
  · simp [byFind, ha, Nat.gcd_zero_left]
  by_cases hb : b = 0
  · simp [byFind, ha, hb, Nat.gcd_zero_right]
  have hpa : 0 < a := Nat.pos_of_ne_zero ha
  have hpb : 0 < b := Nat.pos_of_ne_zero hb
  rw [byFind, ite_eq_right ha, ite_eq_right hb, List.head?_reverse,
    commonDivisors_last a b hpa hpb]
  rfl

theorem byFind_eq_orig (a b : ℕ) : byFind a b = orig a b := byFind_eq a b

/-! ## `byFoldr` -/

theorem byFoldr_eq (a b : ℕ) : byFoldr a b = Nat.gcd a b := by
  by_cases ha : a = 0
  · simp [byFoldr, ha, Nat.gcd_zero_left]
  by_cases hb : b = 0
  · simp [byFoldr, ha, hb, Nat.gcd_zero_right]
  have hpa : 0 < a := Nat.pos_of_ne_zero ha
  have hpb : 0 < b := Nat.pos_of_ne_zero hb
  have hg : 0 < Nat.gcd a b := Nat.gcd_pos_of_pos_left b hpa
  rw [byFoldr, ite_eq_right ha, ite_eq_right hb]
  exact foldr_latch (commonDivisors a b) (Nat.gcd a b) hg (commonDivisors_last a b hpa hpb)

theorem byFoldr_eq_orig (a b : ℕ) : byFoldr a b = orig a b := byFoldr_eq a b

/-! ## `byProductLcm` -/

/-- `gcd a b * lcm a b = a * b`, so with a positive gcd the quotient inverts the
identity. -/
theorem byProductLcm_eq (a b : ℕ) : byProductLcm a b = Nat.gcd a b := by
  by_cases ha0 : a = 0
  · simp [byProductLcm, ha0, Nat.gcd_zero_left]
  by_cases hb0 : b = 0
  · simp [byProductLcm, ha0, hb0, Nat.gcd_zero_right]
  have hpa : 0 < a := Nat.pos_of_ne_zero ha0
  have hpb : 0 < b := Nat.pos_of_ne_zero hb0
  have hl := Nat.lcm_pos hpa hpb
  have hrec := Nat.lcm_mul_gcd a b
  rw [byProductLcm, ite_eq_right ha0, ite_eq_right hb0, ← hrec, Nat.mul_comm,
    Nat.mul_div_cancel (Nat.gcd a b) hl]

theorem byProductLcm_eq_orig (a b : ℕ) : byProductLcm a b = orig a b := byProductLcm_eq a b

end Alt.Nat.gcd
