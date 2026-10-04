import Lynth.Interval.Fns.Elem
import Lynth.Interval.Fns.StirlingExpansion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-!
# Gamma function

Rigorous interval enclosure of `Real.Gamma` following FLINT/Arb
(`arb_hypgeom_gamma`, Fredrik Johansson): argument shifting with the
recurrence `Γ(x+1) = x·Γ(x)` until `z = x + r ≥ T`, Stirling expansion of
`log Γ(z)` with an explicit remainder bound, then `Γ(z) = exp (log Γ z)`
divided by the rising factorial.  Nonpositive arguments go through Euler's
reflection formula `Γ(x)·Γ(1-x) = π / sin(πx)`; general intervals are split
at `0` and the pieces joined with `hull`.

The per-function proof obligations that follow from Mathlib facts
(recurrence chaining, reflection, interval composition) are proved here.
The one analytic input — the Stirling expansion with remainder on
`[8, ∞)` — is proved in `StirlingExpansion` and instantiated here as
`stirling_logGamma` (see its docstring).  It is used at every runtime
evaluation, so proving it once (however long that takes) fixes the
soundness of all Gamma goals; everything in this file is proved from
Mathlib facts, with no axioms and no `sorry`.

Speed notes (runtime matters more than proof length here):
* the hot loop is Horner in `z⁻²` (`stirlingAcc`, structural recursion on a
  `Nat` fuel) plus a short rising-factorial fold; no `ℚ` or well-founded
  recursion in the hot path, so both native and kernel checking stay fast;
* `N` (number of Stirling terms) is chosen adaptively by `chooseN`
  (pure computation, no proofs needed — any `N` is sound);
* `stirlingCoeff` is hybrid: exact `ℚ` literals below 24, values from a
  structural Bernoulli recurrence (`bernoulliList`, evaluated once per
  point) beyond — unbounded term counts, hence no precision ceiling.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Stirling coefficients -/

/-- table values `B_{2k} / (2k * (2k-1))` for `k = 1..24` (`0` beyond;
used below the cutoff — see `stirlingCoeff`). -/
def stirlingTable : Nat → ℚ
  | 1 => 1 / 12
  | 2 => -1 / 360
  | 3 => 1 / 1260
  | 4 => -1 / 1680
  | 5 => 1 / 1188
  | 6 => -691 / 360360
  | 7 => 1 / 156
  | 8 => -3617 / 122400
  | 9 => 43867 / 244188
  | 10 => -174611 / 125400
  | 11 => 77683 / 5796
  | 12 => -236364091 / 1506960
  | 13 => 657931 / 300
  | 14 => -3392780147 / 93960
  | 15 => 1723168255201 / 2492028
  | 16 => -7709321041217 / 505920
  | 17 => 151628697551 / 396
  | 18 => -26315271553053477373 / 2418179400
  | 19 => 154210205991661 / 444
  | 20 => -261082718496449122051 / 21106800
  | 21 => 1520097643918070802691 / 3109932
  | 22 => -2530297234481911294093 / 118680
  | 23 => 25932657025822267968607 / 25380
  | 24 => -5609403368997817686249127547 / 104700960
  | _ => 0

/-! ### General Bernoulli computation (arbitrary `k`) -/

/-- one Pascal-triangle step on adjacent pairs. -/
def pascalAdd : Nat → List Nat → List Nat
  | prev, [] => [prev]
  | prev, x :: xs => (prev + x) :: pascalAdd x xs

theorem length_pascalAdd (prev : Nat) (r : List Nat) :
    (pascalAdd prev r).length = r.length + 1 := by
  induction r generalizing prev with
  | nil => rfl
  | cons x xs ih =>
    have e : pascalAdd prev (x :: xs) = (prev + x) :: pascalAdd x xs := rfl
    have h := ih x
    simp only [e, List.length_cons, h]

/-- next Pascal row from the current one. -/
def nextPascal : List Nat → List Nat
  | [] => [1]
  | _ :: r => 1 :: pascalAdd 1 r

theorem length_nextPascal (r : List Nat) :
    (nextPascal r).length = r.length + 1 := by
  cases r with
  | nil => rfl
  | cons a r =>
    have e : nextPascal (a :: r) = 1 :: pascalAdd 1 r := rfl
    have h := length_pascalAdd 1 r
    simp only [e, List.length_cons, h]

/-- incremental Bernoulli state: `vals = [B_0, …, B_{L-1}]` with
`L = vals.length`, and `row = C(L+1, ·)` for computing `B_L` next. -/
structure BernState where
  vals : List ℚ
  row : List Nat

/-- the next Bernoulli number from the state (binomial recurrence
`B_L = -Σ_{k<L} C(L+1,k)·B_k / (L+1)`). -/
def bernNext (st : BernState) : ℚ :=
  -(∑ k ∈ Finset.range st.vals.length, (st.row.getD k 0 : ℚ) * st.vals.getD k 0) /
    ((st.vals.length : ℚ) + 1)

/-- one step: append `B_L`, advance the Pascal row. -/
def bernStep (st : BernState) : BernState :=
  ⟨st.vals ++ [bernNext st], nextPascal st.row⟩

/-- iterate from `[B_0] = [1]` with row `C(2, ·)`; `vals` grows by append. -/
def bernState : Nat → BernState
  | 0 => ⟨[1], [1, 2, 1]⟩
  | n + 1 => bernStep (bernState n)

theorem length_bernState_vals (n : Nat) : (bernState n).vals.length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have e : (bernState (n + 1)).vals
        = (bernState n).vals ++ [bernNext (bernState n)] := rfl
    simp [e, List.length_append, ih]

/-- `[B_0, …, B_N]` (length `N+1`). -/
def bernoulliList (N : Nat) : List ℚ := (bernState N).vals

/-- computed `n`-th Bernoulli number. -/
def bernoulliQ (n : Nat) : ℚ := (bernoulliList n).getD n 0

/-- quotient form shared by the spec and the Horner entries. -/
def stirlingQuot (b : ℚ) (k : Nat) : ℚ := b / ((2 * (k : ℚ)) * (2 * (k : ℚ) - 1))

/-- general Stirling coefficient for any `k ≥ 1`, computed from Bernoulli. -/
def stirlingGen (k : Nat) : ℚ := stirlingQuot (bernoulliQ (2 * k)) k

/-- hybrid: exact table below the cutoff, computed values beyond
(the cutoff moves with the table; `chooseN` has no cap). -/
def stirlingCoeff (k : Nat) : ℚ :=
  if k ≤ 24 then stirlingTable k else stirlingGen k

/-- `getD` is stable under appending on the right. -/
theorem getD_append_left {α : Type} (l₁ l₂ : List α) (i : Nat) (d : α)
    (h : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  induction l₁ generalizing i with
  | nil => simp at h
  | cons a t ih =>
    cases i with
    | zero => rfl
    | succ i => exact ih i (by simpa using h)

/-- growing the state preserves all computed Bernoulli numbers. -/
theorem bernState_getD_stable (n k i : Nat) (hi : i ≤ n) :
    ((bernState (n + k)).vals.getD i (0 : ℚ)) =
      ((bernState n).vals.getD i (0 : ℚ)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have e : n + (k + 1) = (n + k) + 1 := by omega
    have step : (bernState ((n + k) + 1)).vals
        = (bernState (n + k)).vals ++ [bernNext (bernState (n + k))] := rfl
    have hlen := length_bernState_vals (n + k)
    rw [e, step, getD_append_left _ _ _ _ (by omega), ih]

/-- usable form: a longer list agrees with a shorter one on the overlap. -/
theorem bernoulliList_getD_stable {a b i : Nat} (hi : i ≤ a) (hab : a ≤ b) :
    (bernoulliList b).getD i (0 : ℚ) = (bernoulliList a).getD i (0 : ℚ) := by
  obtain ⟨m, rfl⟩ : ∃ m, b = a + m := ⟨b - a, by omega⟩
  show ((bernState (a + m)).vals.getD i (0 : ℚ)) = _
  exact bernState_getD_stable a m i hi

/-- Stirling summand `c_k / z^(2k-1)` (for `k ≥ 1`). -/
noncomputable def stirlingTerm (z : ℝ) (k : ℕ) : ℝ := (stirlingCoeff k : ℝ) / z ^ (2 * k - 1)

/-! ### Stirling expansion with remainder (proved)

The analytic input — Stirling expansion of `log Γ` on `[8, ∞)` with an
explicit remainder — is proved here via `StirlingExpansion` (Euler–Maclaurin
summation on `log`, transferred from `log (n!)` to `log Γ` by Bohr–Mollerup).
The Bernoulli recurrence and the 24-entry table are verified against
Mathlib's `bernoulli` below, so every coefficient the kernel evaluates is
the Bernoulli quotient the analysis is about.  No axioms, no `sorry`.
-/

lemma pascalAdd_choose (L : ℕ) : ∀ r a : ℕ, a + r = L →
    pascalAdd (L.choose a) ((List.range' (a + 1) r).map L.choose) =
      (List.range' (a + 1) (r + 1)).map (L + 1).choose := by
  intro r
  induction r with
  | zero =>
    intro a h
    subst h
    simp [pascalAdd]
  | succ r ih =>
    intro a h
    rw [List.range'_succ, List.map_cons, pascalAdd, ih (a + 1) (by omega), List.range'_succ (s := a + 1) (n := r + 1),
      List.map_cons, Nat.choose_succ_succ]

lemma nextPascal_choose (L : ℕ) :
    nextPascal ((List.range' 0 (L + 1)).map L.choose) = (List.range' 0 (L + 2)).map (L + 1).choose := by
  rw [List.range'_succ, List.map_cons, nextPascal, List.range'_succ (s := 0) (n := L + 1), List.map_cons]
  have := pascalAdd_choose L L 0 (by omega)
  simp only [Nat.choose_zero_right] at this ⊢
  rw [this]

lemma bernState_spec (n : ℕ) :
    (bernState n).vals.length = n + 1 ∧
    (∀ i ≤ n, (bernState n).vals.getD i 0 = bernoulli i) ∧
    (bernState n).row = (List.range' 0 (n + 3)).map (n + 2).choose := by
  induction n with
  | zero =>
    refine ⟨rfl, ?_, by decide⟩
    intro i hi
    obtain rfl : i = 0 := by omega
    simp [bernState]
  | succ n ih =>
    obtain ⟨hlen, hval, hrow⟩ := ih
    have hnext : bernNext (bernState n) = bernoulli (n + 1) := by
      have hs := sum_bernoulli (n + 2)
      rw [ite_eq_right (show n + 2 ≠ 1 by omega), Finset.sum_range_succ, Nat.choose_succ_self_right] at hs
      unfold bernNext
      rw [hlen]
      have hsum : ∑ k ∈ Finset.range (n + 1),
          ((bernState n).row.getD k 0 : ℚ) * (bernState n).vals.getD k 0 =
          ∑ k ∈ Finset.range (n + 1), ((n + 2).choose k : ℚ) * bernoulli k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [Finset.mem_range] at hk
        rw [hval k (by omega), hrow]
        congr 1
        simp [List.getD_eq_getElem?_getD, show k < n + 3 by omega]
      rw [hsum]
      push_cast at hs ⊢
      field_simp
      linarith
    refine ⟨?_, ?_, ?_⟩
    · simp [bernState, bernStep, hlen]
    · intro i hi
      simp only [bernState, bernStep]
      rcases Nat.lt_or_ge i (n + 1) with h | h
      · rw [List.getD_append _ _ _ _ (by omega), hval i (by omega)]
      · obtain rfl : i = n + 1 := by omega
        rw [List.getD_append_right _ _ _ _ (by omega), hlen, Nat.sub_self]
        simpa using hnext
    · simp only [bernState, bernStep, hrow]
      exact nextPascal_choose (n + 2)

/-- `bernoulliList n` really lists Bernoulli numbers (helper form of (2)). -/
lemma bernoulliList_getD (n i : Nat) (hi : i ≤ n) :
    (bernoulliList n).getD i 0 = bernoulli i :=
  (bernState_spec n).2.1 i hi

/-- Boolean certificate that the first `K` table entries equal the Bernoulli
quotients computed by the recurrence (all Bernoulli numbers computed once, by
`bernoulliList (2 * K)`). Checked by the kernel with `decide +kernel`. -/
def stirlingTableCheck (K : ℕ) : Bool :=
  let L := bernoulliList (2 * K)
  (List.range K).all fun i =>
    stirlingTable (i + 1) == stirlingQuot (L.getD (2 * (i + 1)) 0) (i + 1)

/-- Generic table-correctness lemma: any cutoff `K` whose certificate evaluates to
`true` gives the Bernoulli formula for all entries `1..K`. -/
lemma stirlingTable_eq_of_check {K : ℕ} (h : stirlingTableCheck K = true) {k : ℕ}
    (h1 : 1 ≤ k) (hK : k ≤ K) : stirlingTable k = stirlingQuot (bernoulli (2 * k)) k := by
  unfold stirlingTableCheck at h
  rw [List.all_eq_true] at h
  have := h (k - 1) (List.mem_range.mpr (by omega))
  rw [beq_iff_eq, show k - 1 + 1 = k by omega, bernoulliList_getD _ _ (by omega)] at this
  exact this

/-- The concrete certificate for the 24-entry table (kernel evaluation). -/
lemma stirlingTableCheck_24 : stirlingTableCheck 24 = true := by decide +kernel

/-- Every coefficient used by the hybrid scheme is the Bernoulli quotient. -/
lemma stirlingCoeff_eq (k : ℕ) (hk : 1 ≤ k) :
    stirlingCoeff k = stirlingQuot (bernoulli (2 * k)) k := by
  unfold stirlingCoeff
  split_ifs with h
  · exact stirlingTable_eq_of_check stirlingTableCheck_24 hk h
  · unfold stirlingGen bernoulliQ
    rw [bernoulliList_getD _ _ le_rfl]

lemma stirlingCoeff_cast (k : ℕ) (hk : 1 ≤ k) :
    (stirlingCoeff k : ℝ) = StirlingExpansion.bc k := by
  rw [stirlingCoeff_eq k hk, StirlingExpansion.bc, stirlingQuot]
  push_cast
  ring

/-- Stirling expansion of `log Γ` on `[8, ∞)` with explicit
remainder bound, for every `N ≥ 1` (the real case of FLINT's
`acb_gamma_stirling_bound`). -/
theorem stirling_logGamma (z : ℝ) (hz : 8 ≤ z) (N : ℕ) (hN : 1 ≤ N) :
    ∃ R : ℝ, Real.log (Real.Gamma z)
        = (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
          + (∑ k ∈ Finset.range (N - 1), stirlingTerm z (k + 1)) + R
      ∧ |R| ≤ 2 * |(stirlingCoeff N : ℝ)| / z ^ (2 * N - 1) := by
  refine ⟨StirlingExpansion.E (N - 1) z, ?_, ?_⟩
  · have hsum : (∑ k ∈ Finset.range (N - 1), stirlingTerm z (k + 1)) =
        StirlingExpansion.P (N - 1) z := by
      unfold StirlingExpansion.P stirlingTerm
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [stirlingCoeff_cast _ (by omega), show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
    rw [hsum, StirlingExpansion.E, StirlingExpansion.S]
    ring
  · rw [stirlingCoeff_cast N hN]
    exact StirlingExpansion.abs_E_le hN (by linarith)

/-- the recurrence computes Bernoulli numbers. -/
theorem bernoulliList_correct (n i : Nat) (hi : i ≤ n) :
    (bernoulliList n).getD i 0 = bernoulli i := by
  exact bernoulliList_getD n i hi

/-- the table matches the Bernoulli formula on `1..24`. -/
theorem stirlingTable_correct (k : Nat) (h1 : 1 ≤ k) (h24 : k ≤ 24) :
    stirlingTable k
      = bernoulli (2 * k) / (((2 * k : ℕ) : ℚ) * (((2 * k : ℕ) : ℚ) - 1)) := by
  rw [stirlingTable_eq_of_check stirlingTableCheck_24 h1 h24, stirlingQuot]
  push_cast
  ring



/-! ### Argument shift -/

/-- least `r` with `a + r ≥ T`. -/
def gammaShift (a : Dy) (T : Nat) : Nat :=
  if Dy.leB (Dy.ofNat T) a then 0
  else Int.toNat (Int.ceil ((T : ℚ) - a.toRat))

theorem gammaShift_spec (a : Dy) (T : Nat) :
    (T : ℝ) ≤ a.toReal + ((gammaShift a T : ℕ) : ℝ) := by
  unfold gammaShift
  split
  · rename_i h
    have hle : (Dy.ofNat T).toRat ≤ a.toRat := (leB_iff _ _).1 h
    have hT : ((Dy.ofNat T).toRat : ℝ) = (T : ℝ) := by
      simp [toRat_ofNat]
    simp only [Nat.cast_zero, add_zero]
    rw [← hT, toReal_def]
    exact_mod_cast hle
  · rename_i h
    have hlt : a.toRat < (Dy.ofNat T).toRat := lt_of_not_ge (fun h' => h ((leB_iff _ _).2 h'))
    have hT : ((Dy.ofNat T).toRat : ℝ) = (T : ℝ) := by
      simp [toRat_ofNat]
    have hpos : (0 : ℚ) < (T : ℚ) - a.toRat := by
      have : a.toRat < (T : ℚ) := by simpa [toRat_ofNat] using hlt
      linarith
    have hc : (T : ℚ) - a.toRat ≤ (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := Int.le_ceil _
    have hltQ : (0 : ℚ) < (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := lt_of_lt_of_le hpos hc
    have hnn : 0 ≤ Int.ceil ((T : ℚ) - a.toRat) := by
      by_contra hcon
      push Not at hcon
      have hneg : (Int.ceil ((T : ℚ) - a.toRat) : ℚ) < 0 := by exact_mod_cast hcon
      linarith
    have e : ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℚ)
        = (Int.ceil ((T : ℚ) - a.toRat) : ℚ) := by
      have e2 : ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℤ)
          = Int.ceil ((T : ℚ) - a.toRat) := Int.toNat_of_nonneg hnn
      exact_mod_cast e2
    have hq : (T : ℚ) ≤ a.toRat + ((Int.toNat (Int.ceil ((T : ℚ) - a.toRat)) : ℕ) : ℚ) := by
      rw [e]; linarith
    rw [toReal_def]
    exact_mod_cast hq

/-! ### Rising factorial -/

/-- `x * (x+1) * … * (x+r-1)` (real). -/
def risingReal (x : ℝ) : Nat → ℝ
  | 0 => 1
  | r + 1 => risingReal x r * (x + (r : ℝ))

/-- interval rising factorial. -/
def risingIval (w : Nat) (X : Ival) : Nat → Ival
  | 0 => Ival.one
  | r + 1 => Ival.mul w (risingIval w X r) (Ival.add w X (Ival.ofRat w (r : ℚ)))

theorem mem_risingIval {w : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (r : Nat) :
    risingReal x r ∈ risingIval w X r := by
  induction r with
  | zero => simpa [risingReal, risingIval] using Ival.mem_one
  | succ r ih =>
    simp only [risingReal, risingIval]
    have hr : (x + (r : ℝ)) ∈ Ival.add w X (Ival.ofRat w (r : ℚ)) :=
      Ival.mem_add hx (by simpa using Ival.mem_ofRat w (r : ℚ))
    exact Ival.mem_mul ih hr

/-- helper: a zero factor kills the product. -/
theorem risingReal_eq_zero_of {x : ℝ} {r i : Nat} (hi : i < r) (hxi : x + (i : ℝ) = 0) :
    risingReal x r = 0 := by
  induction r with
  | zero => omega
  | succ r ih =>
    simp only [risingReal]
    by_cases h : i < r
    · rw [ih h, zero_mul]
    · have hir : i = r := by omega
      subst hir
      rw [hxi, mul_zero]

/-- recurrence in division form — valid at poles too, because Mathlib's
`Γ` is `0` at nonpositive integers while `_/0 = 0`. -/
theorem gamma_eq_gamma_add_div_rising (x : ℝ) (r : Nat) :
    Real.Gamma x = Real.Gamma (x + (r : ℝ)) / risingReal x r := by
  induction r with
  | zero => simp [risingReal]
  | succ r ih =>
    have hcast : x + ((r + 1 : ℕ) : ℝ) = (x + (r : ℝ)) + 1 := by push_cast; ring
    rw [hcast]
    by_cases h : x + (r : ℝ) = 0
    · have hx : x = -((r : ℕ) : ℝ) := by linarith
      have hzero : risingReal x (r + 1) = 0 := by
        simp only [risingReal]
        rw [h, mul_zero]
      rw [hzero, hx, Real.Gamma_neg_nat_eq_zero]
      have h1 : (-((r : ℕ) : ℝ) + (r : ℝ)) + 1 = 1 := by ring
      rw [h1, Real.Gamma_one, div_zero]
    · have hadd := Real.Gamma_add_one h
      have hR : risingReal x (r + 1) = (x + (r : ℝ)) * risingReal x r := by
        simp [risingReal, mul_comm]
      rw [hadd, hR, mul_div_mul_left _ _ h, ih]

/-! ### Stirling partial sums (Horner in `z⁻²`) -/

/-- `c_{M-j} + W2 * (c_{M-j+1} + …)`: Horner accumulator, `j` levels.
`B` is the shared Bernoulli list (`bernoulliList (2N)`); levels `k ≤ 24`
use exact table literals, deeper levels the recurrence values in `B`. -/
def stirlingAcc (w : Nat) (W2 : Ival) (B : List ℚ) (M : Nat) : Nat → Ival
  | 0 => Ival.zero
  | j + 1 =>
    Ival.add w (Ival.ofRat w (if M - j ≤ 24 then stirlingTable (M - j)
      else stirlingQuot (B.getD (2 * (M - j)) 0) (M - j)))
      (Ival.mul w W2 (stirlingAcc w W2 B M j))

/-- real value of the accumulator. -/
def stirlingAccReal (t : ℝ) (M j : Nat) : ℝ :=
  ∑ i ∈ Finset.range j, (stirlingCoeff (M - j + 1 + i) : ℝ) * t ^ i

theorem mem_stirlingAcc {w : Nat} {W2 : Ival} {M N : Nat} {t : ℝ}
    (ht : t ∈ W2) (hMN : M + 1 ≤ N) {j : Nat} (hj : j ≤ M) :
    stirlingAccReal t M j ∈ stirlingAcc w W2 (bernoulliList (2 * N)) M j := by
  induction j with
  | zero => simpa [stirlingAccReal, stirlingAcc] using Ival.mem_zero
  | succ j ih =>
    have hj' : j ≤ M := by omega
    have hk1 : 1 ≤ M - j := by omega
    have hstab : (bernoulliList (2 * N)).getD (2 * (M - j)) (0 : ℚ)
        = (bernoulliList (2 * (M - j))).getD (2 * (M - j)) (0 : ℚ) :=
      bernoulliList_getD_stable le_rfl (by omega)
    have hXY : (∑ i ∈ Finset.range j, (stirlingCoeff (M - j + (i + 1)) : ℝ) * t ^ (i + 1))
        = ∑ i ∈ Finset.range j, t * ((stirlingCoeff (M - j + 1 + i) : ℝ) * t ^ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have eix : M - j + (i + 1) = M - j + 1 + i := by omega
      rw [eix, pow_succ']
      ring
    have h0 : M - (j + 1) + 1 + 0 = M - j := by omega
    have hS : stirlingAccReal t M (j + 1)
        = (stirlingCoeff (M - j) : ℝ) + t * stirlingAccReal t M j := by
      simp only [stirlingAccReal, Finset.sum_range_succ', h0, pow_zero, mul_one]
      rw [Finset.mul_sum, hXY]
      exact add_comm _ _
    rw [hS]
    simp only [stirlingAcc]
    by_cases h24 : M - j ≤ 24
    · have eS : stirlingCoeff (M - j) = stirlingTable (M - j) := by
        unfold stirlingCoeff; rw [ite_eq_left h24]
      rw [eS, ite_eq_left h24]
      exact Ival.mem_add (Ival.mem_ofRat _ _) (Ival.mem_mul ht (ih hj'))
    · have eS : stirlingCoeff (M - j) = stirlingGen (M - j) := by
        unfold stirlingCoeff; rw [ite_eq_right h24]
      rw [eS]
      unfold stirlingGen bernoulliQ
      rw [ite_eq_right h24, hstab]
      exact Ival.mem_add (Ival.mem_ofRat _ _) (Ival.mem_mul ht (ih hj'))

/-- `z⁻¹ * (c * (z⁻¹ * z⁻¹)^i) = c * (z^(2i+1))⁻¹`. -/
theorem zinv_sq_pow' (z c : ℝ) (i : Nat) :
    z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ i) = c * (z ^ (2 * i + 1))⁻¹ := by
  induction i with
  | zero => simp [mul_comm]
  | succ i ih =>
    have p1 : z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ (i + 1))
        = (z⁻¹ * (c * (z⁻¹ * z⁻¹) ^ i)) * (z⁻¹ * z⁻¹) := by
      rw [pow_succ']; ring
    have e : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by omega
    rw [p1, ih, e]
    have p2 : c * (z ^ (2 * i + 1))⁻¹ * (z⁻¹ * z⁻¹)
        = c * (z ^ (2 * i + 1) * (z * z))⁻¹ := by
      rw [mul_inv_rev, mul_inv_rev]; ring
    have p3 : z ^ (2 * i + 1) * (z * z) = z ^ ((2 * i + 1) + 2) := by
      conv_rhs => rw [pow_add, pow_two]
    rw [p2, p3]

/-- the Horner value times `z⁻¹` is the theorem's partial sum. -/
theorem stirling_sum_eq {z : ℝ} (N : Nat) :
    (∑ k ∈ Finset.range (N - 1), stirlingTerm z (k + 1))
      = z⁻¹ * stirlingAccReal (z⁻¹ * z⁻¹) (N - 1) (N - 1) := by
  simp only [stirlingAccReal, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  have e : 2 * (k + 1) - 1 = 2 * k + 1 := by omega
  have eN : N - 1 - (N - 1) + 1 + k = k + 1 := by omega
  simp only [stirlingTerm, e, eN, div_eq_mul_inv]
  exact (zinv_sq_pow' z _ k).symm

/-! ### Stirling main term and tail -/

/-- `(z-½) * log z - z + log √(2π)`. -/
def stirlingMain (c : Ctx) (w : Nat) (Z : Ival) : Ival :=
  let logZ := logIval c Z
  let sqrt2pi := Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi)
  let logSqrt2pi := logIval c sqrt2pi
  let half := Ival.ofRat w (1 / 2)
  Ival.sub w (Ival.add w (Ival.mul w (Ival.sub w Z half) logZ) logSqrt2pi) Z

theorem mem_stirlingMain {c : Ctx} (hc : c.Valid) {z : ℝ} {Z : Ival} (hx : z ∈ Z) :
    (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMain c w Z := by
  unfold stirlingMain
  simp only
  have hhalf : ((1 / 2 : ℚ) : ℝ) ∈ Ival.ofRat w (1 / 2) := Ival.mem_ofRat _ _
  have h2m : ((2 : ℚ) : ℝ) ∈ Ival.ofRat w 2 := Ival.mem_ofRat _ _
  have e1 : ((1 / 2 : ℚ) : ℝ) = 1 / 2 := by simp
  have e2 : ((2 : ℚ) : ℝ) = 2 := by simp
  rw [e1] at hhalf
  rw [e2] at h2m
  have hsqrt : Real.sqrt (2 * Real.pi)
      ∈ Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi) :=
    Ival.mem_sqrt (Ival.mem_mul h2m hc.pi_mem)
  have h : ((z - 1 / 2) * Real.log z + Real.log (Real.sqrt (2 * Real.pi))) - z
      ∈ Ival.sub w (Ival.add w (Ival.mul w (Ival.sub w Z (Ival.ofRat w (1 / 2)))
        (logIval c Z)) (logIval c (Ival.sqrt w (Ival.mul w (Ival.ofRat w 2) c.pi)))) Z :=
    Ival.mem_sub
      (Ival.mem_add
        (Ival.mem_mul
          (Ival.mem_sub hx hhalf)
          (mem_logIval hc hx))
        (mem_logIval hc hsqrt))
      hx
  have eassoc : (z - 1 / 2) * Real.log z - z + Real.log (Real.sqrt (2 * Real.pi))
      = ((z - 1 / 2) * Real.log z + Real.log (Real.sqrt (2 * Real.pi))) - z := by ring
  rw [eassoc]
  exact h

/-- tail interval from an explicit coefficient (search fast path, no proofs). -/
def stirlingTailIvalQ (w : Nat) (Z : Ival) (N : Nat) (cN : ℚ) : Ival :=
  Ival.div w (Ival.ofRat w (2 * |cN|)) (Ival.npow w Z (2 * N - 1))

/-- interval containing the real remainder bound `2|c_N| / z^(2N-1)`. -/
def stirlingTailIval (w : Nat) (Z : Ival) (N : Nat) : Ival :=
  stirlingTailIvalQ w Z N (stirlingCoeff N)

theorem mem_stirlingTailIval {w : Nat} {Z : Ival} {N : Nat} {z : ℝ}
    (hx : z ∈ Z) :
    2 * |(stirlingCoeff N : ℝ)| / z ^ (2 * N - 1) ∈ stirlingTailIval w Z N := by
  unfold stirlingTailIval
  have hnum : ((2 * |stirlingCoeff N| : ℚ) : ℝ) = 2 * |(stirlingCoeff N : ℝ)| := by
    rw [Rat.cast_mul, Rat.cast_abs, Rat.cast_ofNat]
  have hmem : ((2 * |stirlingCoeff N| : ℚ) : ℝ) ∈ Ival.ofRat w (2 * |stirlingCoeff N|) :=
    Ival.mem_ofRat _ _
  rw [hnum] at hmem
  exact Ival.mem_div hmem (Ival.mem_npow hx _)

/-- `log Γ` on `Z ∋ z ≥ 8`: main + Horner sum widened by the tail.
`B` is the shared Bernoulli list (`bernoulliList (2N)`). -/
def logGammaIval (c : Ctx) (w : Nat) (Z : Ival) (N : Nat) (B : List ℚ) : Ival :=
  let Zinv := Ival.inv w Z
  let W2 := Ival.mul w Zinv Zinv
  let S := Ival.mul w Zinv (stirlingAcc w W2 B (N - 1) (N - 1))
  let M := stirlingMain c w Z
  Ival.widenMag w (Ival.add w M S) (Ival.magHi (stirlingTailIval w Z N))

theorem mem_logGammaIval {c : Ctx} (hc : c.Valid) {w : Nat} {Z : Ival} {N : Nat} {zz : ℝ}
    (hx : zz ∈ Z) (hz : 8 ≤ zz) (hN1 : 1 ≤ N) :
    Real.log (Real.Gamma zz) ∈ logGammaIval c w Z N (bernoulliList (2 * N)) := by
  obtain ⟨R, hR, hRb⟩ := stirling_logGamma zz hz N hN1
  have hMN : N - 1 + 1 ≤ N := by omega
  have hzi : zz⁻¹ ∈ Ival.inv w Z := Ival.mem_inv hx
  have hW2 : zz⁻¹ * zz⁻¹ ∈ Ival.mul w (Ival.inv w Z) (Ival.inv w Z) :=
    Ival.mem_mul hzi hzi
  have hS : (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))
      ∈ Ival.mul w (Ival.inv w Z)
        (stirlingAcc w (Ival.mul w (Ival.inv w Z) (Ival.inv w Z))
          (bernoulliList (2 * N)) (N - 1) (N - 1)) := by
    rw [stirling_sum_eq]
    exact Ival.mem_mul hzi (mem_stirlingAcc hW2 hMN le_rfl)
  have hM : (zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi))
      ∈ stirlingMain c w Z := mem_stirlingMain (c := c) (w := w) hc hx
  have hMS : ((zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi)))
      + (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))
      ∈ Ival.add w (stirlingMain c w Z)
        (Ival.mul w (Ival.inv w Z)
          (stirlingAcc w (Ival.mul w (Ival.inv w Z) (Ival.inv w Z))
            (bernoulliList (2 * N)) (N - 1) (N - 1))) :=
    Ival.mem_add hM hS
  have hT : 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1)
      ∈ stirlingTailIval w Z N := mem_stirlingTailIval (w := w) (N := N) hx
  unfold logGammaIval
  simp only
  apply Ival.mem_widenMag hMS
  intro m hm
  have hB : 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1) ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  -- `|R| ≤ bound ≤ m`, and `logΓ - (main + S) = R`
  have hReq : Real.log (Real.Gamma zz)
      - (((zz - 1 / 2) * Real.log zz - zz + Real.log (Real.sqrt (2 * Real.pi)))
        + (∑ k ∈ Finset.range (N - 1), stirlingTerm zz (k + 1))) = R := by
    linarith [hR]
  rw [hReq]
  have hBnn : 0 ≤ 2 * |(stirlingCoeff N : ℝ)| / zz ^ (2 * N - 1) := by positivity
  have := abs_le.1 hRb
  linarith

/-! ### Adaptive parameter choice (pure computation, no proofs needed) -/

/-- is the tail bound at the threshold point already below `2^{-(w+8)}`?
`cN` is the candidate coefficient value (from the threaded Bernoulli state). -/
def tailSmallQ (w T N : Nat) (cN : ℚ) : Bool :=
  match Ival.magHi (stirlingTailIvalQ w (Ival.pt (Dy.ofNat T)) N cN) with
  | some m => Dy.leB m ⟨1, -((w + 8 : Nat) : Int)⟩
  | none => false

/-- smallest `N ≥ 1` with a small tail bound (no cap — any `N` is sound).
The Bernoulli state is threaded through so the whole search costs `O(N²)`
instead of recomputing the recurrence per candidate. -/
def chooseN (w T : Nat) : Nat := go (w + 64) 1 (bernState 2)
where go : Nat → Nat → BernState → Nat
  | 0, N, _ => N
  | fuel + 1, N, st =>
    if tailSmallQ w T N (stirlingQuot (st.vals.getD (2 * N) 0) N) then N
    else go fuel (N + 1) (bernStep (bernStep st))

theorem chooseN_go_ge_one {w T : Nat} : ∀ fuel N st, 1 ≤ N → 1 ≤ chooseN.go w T fuel N st
  | 0, _, _, h => by simp [chooseN.go, h]
  | fuel + 1, _, _, h => by
    unfold chooseN.go
    split
    · exact h
    · exact chooseN_go_ge_one fuel _ _ (by omega)

theorem chooseN_ge_one {w T : Nat} : 1 ≤ chooseN w T :=
  chooseN_go_ge_one _ _ _ le_rfl

/-! ### Positive side: shift + Stirling + rising -/

/-- `Γ` for any interval `X` (tight when `X` is positive and narrow):
shift `r` so `Z = X + r ≥ T`, Stirling `log Γ` on `Z`, `exp`, divide by
the rising factorial. -/
def gammaPosIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 16
  let T := Nat.max 10 (w / 8)
  match X.lo with
  | none => Ival.top
  | some a =>
    let r := gammaShift a T
    let Z := Ival.add w X (Ival.pt (Dy.ofNat r))
    let N := chooseN w T
    Ival.div w (expIval c (logGammaIval c w Z N (bernoulliList (2 * N)))) (risingIval w X r)

theorem mem_gammaPosIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) : Real.Gamma x ∈ gammaPosIval c X := by
  unfold gammaPosIval
  simp only
  split
  · exact Ival.mem_top _
  · rename_i a ha
    set w := c.prec + 16
    set T := Nat.max 10 (w / 8)
    set r := gammaShift a T
    set N := chooseN w T
    have hax := hx.1 a ha
    have hr : (T : ℝ) ≤ a.toReal + ((r : ℕ) : ℝ) := gammaShift_spec a T
    have hzT : (T : ℝ) ≤ x + ((r : ℕ) : ℝ) := by
      have := add_le_add_right hax (((r : ℕ) : ℝ))
      linarith
    have h10 : (10 : ℝ) ≤ (T : ℝ) := by
      exact_mod_cast Nat.le_max_left 10 (w / 8)
    have h8 : 8 ≤ x + ((r : ℕ) : ℝ) := by linarith
    have hZ : x + ((r : ℕ) : ℝ) ∈ Ival.add w X (Ival.pt (Dy.ofNat r)) :=
      Ival.mem_add hx (Ival.mem_pt_nat r)
    have hL := mem_logGammaIval (w := w) (N := chooseN w T) hc hZ h8
      chooseN_ge_one
    have hpos : 0 < Real.Gamma (x + ((r : ℕ) : ℝ)) :=
      Real.Gamma_pos_of_pos (by linarith)
    have hG : Real.Gamma (x + ((r : ℕ) : ℝ)) ∈ expIval c (logGammaIval c w
        (Ival.add w X (Ival.pt (Dy.ofNat r))) N (bernoulliList (2 * N))) := by
      rw [← Real.exp_log hpos]
      exact mem_expIval c hL
    have hRr := mem_risingIval (w := w) hx r
    have e := gamma_eq_gamma_add_div_rising x r
    rw [e]
    exact Ival.mem_div hG hRr

/-! ### Reflection for `hi < 1` -/

/-- `Γ` via `Γ(x) = (π / sin(πx)) / Γ(1-x)`. -/
def gammaReflIval (c : Ctx) (X : Ival) : Ival :=
  let w := c.prec + 16
  let S := sinIval c (Ival.mul w c.pi X)
  let G := gammaPosIval c (Ival.sub w Ival.one X)
  Ival.div w (Ival.div w c.pi S) G

theorem mem_gammaReflIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) (hne : Real.Gamma (1 - x) ≠ 0) :
    Real.Gamma x ∈ gammaReflIval c X := by
  have hsin : Real.sin (Real.pi * x)
      ∈ sinIval c (Ival.mul (c.prec + 16) c.pi X) :=
    mem_sinIval hc (Ival.mem_mul hc.pi_mem hx)
  have hG : Real.Gamma (1 - x)
      ∈ gammaPosIval c (Ival.sub (c.prec + 16) Ival.one X) :=
    mem_gammaPosIval hc (Ival.mem_sub Ival.mem_one hx)
  have hrefl := Real.Gamma_mul_Gamma_one_sub x
  have e : Real.Gamma x
      = (Real.pi / Real.sin (Real.pi * x)) / Real.Gamma (1 - x) :=
    (eq_div_iff hne).mpr hrefl
  unfold gammaReflIval
  simp only
  rw [e]
  exact Ival.mem_div (Ival.mem_div hc.pi_mem hsin) hG

/-! ### Top-level dispatch: split at `0` -/

/-- `X.hi < 1`? -/
def hiLtOne (X : Ival) : Bool :=
  match X.hi with | some b => Dy.ltB b Dy.one | none => false

theorem hiLtOne_mem {x : ℝ} {X : Ival} (hx : x ∈ X) (h : hiLtOne X = true) : x < 1 := by
  unfold hiLtOne at h
  split at h
  · rename_i b hb
    have hxb := hx.2 b hb
    have hlt := toReal_lt_of_ltB h
    have h1 : (Dy.one).toReal = 1 := by simp [toReal_def]
    linarith
  · simp at h

/-- `X ∩ (-∞, 0]`. -/
def negPart (X : Ival) : Ival :=
  ⟨X.lo, some (match X.hi with | some b => Dy.min b Dy.zero | none => Dy.zero)⟩

/-- `X ∩ [0, ∞)`. -/
def posPart (X : Ival) : Ival :=
  ⟨some (match X.lo with | some a => Dy.max a Dy.zero | none => Dy.zero), X.hi⟩

theorem mem_negPart {x : ℝ} {X : Ival} (hx : x ∈ X) (hx0 : x ≤ 0) : x ∈ negPart X := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold negPart
  refine ⟨hx1, ?_⟩
  intro h hh
  cases hhi : X.hi with
  | none => simp [hhi] at hh; subst hh; simp [toReal_def]; exact hx0
  | some b =>
    simp only [hhi, Option.some.injEq] at hh
    subst hh
    have hxb := hx2 b hhi
    have hz : (Dy.zero).toReal = 0 := by simp [toReal_def]
    rcases toRat_min_eq_or b Dy.zero with e | e
    · rw [e]; exact hxb
    · rw [e, hz]; exact hx0

theorem mem_posPart {x : ℝ} {X : Ival} (hx : x ∈ X) (h0x : 0 ≤ x) : x ∈ posPart X := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold posPart
  refine ⟨?_, hx2⟩
  intro a ha
  cases hlo : X.lo with
  | none => simp [hlo] at ha; subst ha; simp [toReal_def]; exact h0x
  | some v =>
    simp only [hlo, Option.some.injEq] at ha
    subst ha
    have hxv := hx1 v hlo
    have hz : (Dy.zero).toReal = 0 := by simp [toReal_def]
    rcases toRat_max_eq_or v Dy.zero with e | e
    · rw [e]; exact hxv
    · rw [e, hz]; exact h0x

/-- `Γ` on any interval: positive fast path, reflection below `1`,
hull of the two pieces across `0` otherwise. -/
def gammaIval (c : Ctx) (X : Ival) : Ival :=
  if X.pos then gammaPosIval c X
  else if hiLtOne X then gammaReflIval c X
  else Ival.hull (gammaReflIval c (negPart X)) (gammaPosIval c (posPart X))

theorem mem_gammaIval {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival}
    (hx : x ∈ X) : Real.Gamma x ∈ gammaIval c X := by
  unfold gammaIval
  split
  · exact mem_gammaPosIval hc hx
  · rename_i hpos
    split
    · rename_i h1
      have hx1 := hiLtOne_mem hx h1
      have hne : Real.Gamma (1 - x) ≠ 0 :=
        ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
      exact mem_gammaReflIval hc hx hne
    · rename_i h1
      rcases le_total x 0 with hx0 | h0x
      · have hne : Real.Gamma (1 - x) ≠ 0 :=
          ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
        exact Ival.mem_hull_left (mem_gammaReflIval hc (mem_negPart hx hx0) hne)
      · exact Ival.mem_hull_right (mem_gammaPosIval hc (mem_posPart hx h0x))

@[lynth_fn] def gammaR : Fn1 .real .real where
  name := "gamma"
  graph x y := y = Real.Gamma x
  exu := exu_eq _
  ev := gammaIval
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_gammaIval hc hx
  cost := 500

end Lynth.Interval.Fns
