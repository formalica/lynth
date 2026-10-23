module

public import Init.Data.List.Basic
public import Init.Prelude
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib

/-! Ported from `/tmp/zeta/zeta_eulerprod_thm.lean` (external prover, complete).
`Euler-product` theory for real zeta. -/

namespace Lynth.Interval.Fns

/-!
# Euler product for integer zeta (FLINT's integer path) — PROVED by external prover

This file is self-contained modulo Mathlib (no Lynth dependency).
It contains the exact statements needed to compute `ζ(n)` for integers
`n ≥ 2` the way FLINT does (`src/arb/zeta_ui.c`,
`src/acb_dirichlet/euler_product_real_ui.c`): the partial Euler product
over primes `≤ P` plus an explicit tail bound.

## The formula

For integers `n ≥ 2` and cutoff `P ≥ 2`, with
`Π(n, P) = ∏_{p ≤ P, prime} (1 - p⁻ⁿ)⁻¹` (reals):

```
|ζ(n) - Π(n, P)| ≤ 2 / (P^{n-1} · (n - 1))
```

where `ζ(n) = (riemannZeta n).re`.  Proof sketch (FLINT bounds the same
quantity via `mag_hurwitz_zeta_uiui`): `Π · ∏_{p≤P}(1-p⁻ⁿ) = 1`, and
`ζ(n)·∏_{p≤P}(1-p⁻ⁿ) = Σ_{m P-rough} m⁻ⁿ = 1 + R` with
`0 ≤ R ≤ Σ_{m≥P+1} m⁻ⁿ ≤ P^{1-n}/(n-1)` (integral comparison); hence
`ζ(n) = Π·(1+R)` and `|ζ(n) - Π| = Π·R ≤ Π·P^{1-n}/(n-1)`, with
`Π ≤ ζ(n) ≤ ζ(2) = π²/6 < 2`.

## Task

Replace each `sorrry` below with a real proof. Statements must stay
byte-identical (they will be mirrored into Lynth as axioms first, then
as theorems). Difficulty labels: the MASTER bound is the hard one; the
rest is scaffolding of increasing easiness.

## References

* FLINT `src/arb/zeta_ui.c` (`arb_zeta_ui_euler_product`,
  `euler_product_cutoff`), `src/acb_dirichlet/euler_product_real_ui.c`
  (`_acb_dirichlet_euler_product_real_ui`: product `∏(1-p⁻ˢ)`, early break
  when the tail is negligible, `mag_hurwitz_zeta_uiui` tail bound).
* Mathlib `EulerProduct/Basic.lean`, `DirichletLSeries.lean` (Euler products),
  `NumberTheory/ZetaValues.lean` (`hasSum_zeta_two`: `ζ(2) = π²/6`).

## Acceptance criteria

* Toolchain `leanprover/lean4:v4.34.0`, Mathlib `v4.34.0`.
* No `sorrry`, no new `axiom` (any Mathlib lemmas may be used).
* Constants (`2`, threshold `P ≥ 2`) follow the sketch above; the prover may
  adjust them with justification if the proof needs it.
-/

open Real BigOperators Topology Filter Finset Nat

/-- primes `≤ P` (mirrors Lynth's sieve). -/
@[expose] public def eulerPrimes (P : Nat) : List Nat := (List.range (P + 1)).filter Nat.Prime

/-- partial Euler product `Π(n, P)` (reals). -/
noncomputable def eulerProd (n P : Nat) : ℝ :=
  ((eulerPrimes P).map fun p => (1 : ℝ) / (1 - 1 / (p ^ n : ℝ))).prod

/-- EASY: sieve membership. -/
theorem eulerPrimes_mem {P p : Nat} : p ∈ eulerPrimes P ↔ p.Prime ∧ p ≤ P := by
  simp [eulerPrimes, List.mem_filter, List.mem_range, and_comm]

/-- EASY: every factor exceeds `1` (so `Π` is increasing in `P`). -/
theorem eulerProd_factor_gt_one {n P : Nat} (hn : 2 ≤ n) (p : Nat)
    (hp : p ∈ eulerPrimes P) : 1 < (1 : ℝ) / (1 - 1 / (p ^ n : ℝ)) := by
  have h2 : 2 ≤ p := (eulerPrimes_mem.mp hp).1.two_le
  have hp1 : (1 : ℝ) < (p : ℝ) ^ n := by
    have : (1 : ℝ) < p := by exact_mod_cast h2
    exact one_lt_pow₀ this (by omega)
  have hq : 0 < 1 / ((p : ℝ) ^ n) := by positivity
  have hq1 : 1 / ((p : ℝ) ^ n) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-! ### Auxiliary material (Euler product as a sum over smooth numbers) -/

/-- `m ↦ m⁻ⁿ` as a completely multiplicative function. -/
noncomputable def zpowHom (n : ℕ) : ℕ →* ℝ where
  toFun m := ((m : ℝ) ^ n)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_pow, mul_inv]

lemma zpowHom_apply (n m : ℕ) : zpowHom n m = 1 / ((m : ℝ) ^ n) := by
  simp [zpowHom]

lemma zpowHom_nonneg (n m : ℕ) : 0 ≤ zpowHom n m := by
  rw [zpowHom_apply]; positivity

lemma summable_zpowHom {n : ℕ} (hn : 2 ≤ n) : Summable (fun m => zpowHom n m) := by
  simp only [zpowHom_apply]
  exact Real.summable_one_div_nat_pow.mpr (by omega)

/-- the partial Euler product is the sum of `m⁻ⁿ` over `(P+1)`-smooth `m`. -/
lemma eulerProd_eq_tsum_smooth {n : ℕ} (hn : 2 ≤ n) (P : ℕ) :
    eulerProd n P = ∑' m : (P + 1).smoothNumbers, zpowHom n m := by
  rw [← EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers (summable_zpowHom hn)]
  unfold eulerProd
  rw [Finset.prod_eq_multiset_prod]
  have : (Nat.primesBelow (P+1)).val = (eulerPrimes P : Multiset ℕ) := by
    simp [Nat.primesBelow, eulerPrimes, Finset.filter_val, Finset.range_val, Multiset.range]
  rw [this, Multiset.map_coe, Multiset.prod_coe]
  congr 1
  simp only [one_div, zpowHom_apply]
  induction (eulerPrimes P) <;> simp_all

lemma zeta_re_eq_tsum {n : ℕ} (hn : 2 ≤ n) :
    (riemannZeta (n : ℂ)).re = ∑' m : ℕ, zpowHom n m := by
  rw [zeta_nat_eq_tsum_of_gt_one (by omega)]
  simp only [zpowHom_apply]
  rw [show (∑' m : ℕ, 1 / (m : ℂ) ^ n) = ((∑' m : ℕ, 1 / (m : ℝ) ^ n : ℝ) : ℂ) by
    rw [Complex.ofReal_tsum]; push_cast; rfl]
  exact Complex.ofReal_re _

/-- `ζ(n) - Π(n,P)` is the sum of `m⁻ⁿ` over the non-`(P+1)`-smooth `m`. -/
lemma zeta_sub_eulerProd_eq {n : ℕ} (hn : 2 ≤ n) (P : ℕ) :
    (riemannZeta (n : ℂ)).re - eulerProd n P
      = ∑' m : ↥((P + 1).smoothNumbersᶜ), zpowHom n m := by
  rw [zeta_re_eq_tsum hn, eulerProd_eq_tsum_smooth hn,
    ← (summable_zpowHom hn).tsum_subtype_add_tsum_subtype_compl ((P + 1).smoothNumbers)]
  ring

lemma zeta_sub_eulerProd_nonneg {n : ℕ} (hn : 2 ≤ n) (P : ℕ) :
    0 ≤ (riemannZeta (n : ℂ)).re - eulerProd n P := by
  rw [zeta_sub_eulerProd_eq hn]
  exact tsum_nonneg fun m => zpowHom_nonneg n m

/-- non-smooth numbers are large: the non-`(P+1)`-smooth sum is bounded by the
tail `Σ_{m ≥ P+1} m⁻ⁿ`. -/
lemma zeta_sub_eulerProd_le_tail {n : ℕ} (hn : 2 ≤ n) (P : ℕ) :
    (riemannZeta (n : ℂ)).re - eulerProd n P
      ≤ ∑' m : {m : ℕ // P + 1 ≤ m}, (1 : ℝ) / (m ^ n : ℝ) := by
  rw [zeta_sub_eulerProd_eq hn]
  have e : (∑' m : {m : ℕ // P + 1 ≤ m}, (1 : ℝ) / (m ^ n : ℝ))
      = ∑' m : ({m : ℕ | P + 1 ≤ m} : Set ℕ), zpowHom n m := by
    simp only [zpowHom_apply]; rfl
  rw [e, _root_.tsum_subtype, _root_.tsum_subtype]
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ ?_
  · by_cases hm : m ∈ ((P + 1).smoothNumbers)ᶜ
    · have hm' : m ∈ ({m : ℕ | P + 1 ≤ m} : Set ℕ) ∨ m = 0 := by
        by_cases h0 : m = 0
        · exact Or.inr h0
        left
        simp only [Set.mem_compl_iff, Nat.mem_smoothNumbers', not_forall, not_lt] at hm
        obtain ⟨p, hp, hpm, hle⟩ := hm
        exact le_trans hle (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hpm)
      rcases hm' with hm' | rfl
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem hm']
      · rw [Set.indicator_of_mem hm, zpowHom_apply]
        simp [show n ≠ 0 by omega]
    · rw [Set.indicator_of_notMem hm]
      exact Set.indicator_nonneg (fun m _ => zpowHom_nonneg n m) m
  · exact (summable_zpowHom hn).indicator _
  · exact (summable_zpowHom hn).indicator _

/-- MEDIUM: partial products are below `ζ(n)` (each factor `> 1`, and the
full product is `ζ(n)`; use the Euler-product identity from Mathlib). -/
theorem eulerProd_le_zeta {n P : Nat} (hn : 2 ≤ n) :
    eulerProd n P ≤ (riemannZeta (n : ℂ)).re := by
  linarith [zeta_sub_eulerProd_nonneg hn P]

/-- MEDIUM: `ζ(2) < 2` (via `π²/6`). -/
theorem zeta_two_lt_two : (riemannZeta (2 : ℂ)).re < 2 := by
  rw [riemannZeta_two]
  have h : ((π : ℂ) ^ 2 / 6) = ((π ^ 2 / 6 : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.ofReal_re]
  have := Real.pi_lt_d2
  have := Real.pi_pos
  nlinarith

/-- MEDIUM: integral tail `Σ_{m≥P+1} m⁻ⁿ ≤ P^{1-n}/(n-1)` for `2 ≤ n`. -/
theorem nat_tail_bound {n P : Nat} (hn : 2 ≤ n) (hP : 2 ≤ P) :
    ∑' m : {m : ℕ // P + 1 ≤ m}, (1 : ℝ) / (m ^ n : ℝ)
      ≤ (P : ℝ) ^ (1 - (n : ℝ)) / ((n : ℝ) - 1) := by
  let e : ℕ ≃ {m : ℕ // P + 1 ≤ m} :=
    ⟨fun i => ⟨i + (P + 1), by omega⟩, fun m => m.1 - (P + 1), fun i => by simp,
      fun m => by ext; simp; have := m.2; omega⟩
  rw [← e.tsum_eq]
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  refine Real.tsum_le_of_sum_range_le (fun i => by positivity) (fun a => ?_)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(n : ℝ))) (Set.Icc (P : ℝ) (P + a)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  have hint : ∫ x in (P : ℝ)..P + a, x ^ (-(n : ℝ))
      = ((P + a : ℝ) ^ (-(n : ℝ) + 1) - (P : ℝ) ^ (-(n : ℝ) + 1)) / (-(n : ℝ) + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [hint] at h1
  have hterm : ∀ i ∈ Finset.range a, (1 : ℝ) / (((e i : ℕ) : ℝ) ^ n)
      = (fun x : ℝ => x ^ (-(n : ℝ))) (P + ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    simp only [e, Equiv.coe_fn_mk]
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hterm]
  refine h1.trans ?_
  have hq : 0 ≤ (P + a : ℝ) ^ (-(n : ℝ) + 1) := by positivity
  rw [show -(n : ℝ) + 1 = 1 - n by ring] at hq ⊢
  rw [show ((P + a : ℝ) ^ (1 - (n : ℝ)) - (P : ℝ) ^ (1 - (n : ℝ))) / (1 - n)
      = ((P : ℝ) ^ (1 - (n : ℝ)) - (P + a : ℝ) ^ (1 - (n : ℝ))) / (n - 1) by
    rw [← neg_sub ((P : ℝ) ^ (1 - (n : ℝ))), ← neg_sub (n : ℝ) 1, neg_div_neg_eq]]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

/-- MAIN: Euler-product tail bound.
For `2 ≤ n`, `2 ≤ P`, `|ζ(n) - Π(n,P)| ≤ 2/((P^{n-1})·(n-1))`. -/
theorem zeta_eulerprod_tail (n P : Nat) (hn : 2 ≤ n) (hP : 2 ≤ P) :
    |(riemannZeta (n : ℂ)).re - eulerProd n P|
      ≤ 2 / (((P ^ (n - 1) : Nat) : ℝ) * ((n : ℝ) - 1)) := by
  rw [abs_of_nonneg (zeta_sub_eulerProd_nonneg hn P)]
  refine (zeta_sub_eulerProd_le_tail hn P).trans ((nat_tail_bound hn hP).trans ?_)
  have hPpos : (0 : ℝ) < P := by exact_mod_cast (show 0 < P by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hpow : (P : ℝ) ^ (1 - (n : ℝ)) = 1 / (((P ^ (n - 1) : Nat) : ℝ)) := by
    rw [show (1 : ℝ) - n = -((n - 1 : ℕ) : ℝ) by
      rw [Nat.cast_sub (by omega)]; push_cast; ring]
    rw [Real.rpow_neg hPpos.le, Real.rpow_natCast]
    push_cast
    rw [one_div]
  have hX : (0 : ℝ) < ((P ^ (n - 1) : Nat) : ℝ) := by positivity
  rw [hpow, div_div]
  exact div_le_div_of_nonneg_right (by norm_num) (by nlinarith)


end Lynth.Interval.Fns
