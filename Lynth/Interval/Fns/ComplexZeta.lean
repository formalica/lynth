module

public import Init.Data.Cast
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Lynth.Interval.Core.Expr
public import Lynth.Interval.Core.Asy
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Fn
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Fns.ComplexElem
public import Lynth.Interval.Fns.ComplexGamma
public import Lynth.Interval.Fns.ComplexZetaEM
public import Lynth.Interval.Fns.Elem
public import Lynth.Interval.Fns.ZetaEulerProd
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Series.Tail
public import Lynth.Interval.Vendor.Dyadic
import Mathlib
import all Lynth.Interval.Fns.Zeta
import all Lynth.Interval.Fns.ComplexGamma
import all Lynth.Interval.Fns.ComplexZetaEM
import all Lynth.Interval.Fns.ComplexElem

/-!
# Complex Riemann zeta via Euler product (`2 ≤ Re`) and functional equation.

Mirror of the real dispatch (`Lynth/Interval/Fns/Zeta.lean`): for
`2 ≤ Re s` the Euler product over `eulerPrimes P` widened by an explicit
tail in `s.re` (no monotonicity argument needed — the tail bound is
evaluated as an interval over the `Re` enclosure); for `Re s ≤ -1` the
functional equation `ζ(s) = 2^s·π^{s-1}·sin(πs/2)·Γ(1-s)·ζ(1-s)` with the
inner value back in the `Re ≥ 2` region.  Point `2` goes through the closed
form `ζ(2) = π²/6` (the Euler tail at `σ = 2` is too wide to be useful, and
the `ζ(-1)` reflection needs a tight `ζ(2)`).

The two analytic inputs — the Euler-product remainder over `ℂ` and the
functional equation solved for `ζ s` — were proved by the external prover
(`/tmp/86f924db-58c6-4375-9ea5-2de8c76ce92e-aristotle.tar.gz`,
`output-final_aristotle/zeta_handoff.lean`) and ported here with two Lean
4.34 adaptations: `smoothNumbers` unfolding in the `indicator` term
(folded back by `rfl`), `if_pos` → `ite_eq_left`.  Everything else is
proved inline.  The strip `(-1, 2)` (critical strip, `ζ(1/2)`, `ζ(3/2)`,
`ζ(-1/2)`, `ζ(3)`, `ζ(5)`, …) needs complex Euler–Maclaurin and is left for
the next batch.
-/

/-! ### Real `p`-series tail lemmas (ported from the zeta handoff).

Helper lemmas for `Complex.eulerprod_tail`, kept at root level exactly as
proved by the external prover. -/

/-- Telescoping step: `(x+1)^{-(a+1)} ≤ (x^{-a} - (x+1)^{-a}) / a` for `a ≥ 1`, `x ≥ 1`. -/
lemma rpow_step_ineq {a x : ℝ} (ha : 1 ≤ a) (hx : 1 ≤ x) :
    (x + 1) ^ (-(a + 1)) ≤ (x ^ (-a) - (x + 1) ^ (-a)) / a := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hb := one_add_mul_self_le_rpow_one_add (s := 1 / x) (by
    have : 0 < 1 / x := by positivity
    linarith) ha
  have e1 : (1 + 1 / x) = (x + 1) / x := by field_simp
  rw [e1, Real.div_rpow hx1.le hx0.le] at hb
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hx1a : 0 < (x + 1) ^ a := Real.rpow_pos_of_pos hx1 a
  rw [le_div_iff₀ hxa] at hb
  rw [Real.rpow_neg hx0.le, Real.rpow_neg hx1.le, Real.rpow_neg hx1.le,
    Real.rpow_add hx1, Real.rpow_one]
  rw [le_div_iff₀ (by linarith), inv_sub_inv hxa.ne' hx1a.ne']
  generalize x ^ a = X at *
  generalize (x + 1) ^ a = Y at *
  rw [inv_mul_eq_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : a * X ≤ x * (Y - X) := by
    have : (1 + a * (1 / x)) * X * x = (x + a) * X := by field_simp
    nlinarith
  have : a * X ≤ (x + 1) * (Y - X) := by nlinarith
  nlinarith [mul_pos hxa hx1a]

lemma sum_Ico_rpow_le {a : ℝ} (ha : 1 ≤ a) (P : ℕ) (hP : 1 ≤ P) (k : ℕ) :
    ∑ n ∈ Finset.Ico (P + 1) (P + 1 + k), ((n : ℕ) : ℝ) ^ (-(a + 1))
      ≤ ((P : ℝ) ^ (-a) - ((P + k : ℕ) : ℝ) ^ (-a)) / a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← add_assoc, Finset.sum_Ico_succ_top (by omega)]
    have h := rpow_step_ineq ha (x := ((P + k : ℕ) : ℝ)) (by
      have : (1:ℝ) ≤ P := by exact_mod_cast hP
      push_cast; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)])
    have e : ((P + 1 + k : ℕ) : ℝ) = ((P + k : ℕ) : ℝ) + 1 := by push_cast; ring
    have e2 : ((P + (k + 1) : ℕ) : ℝ) = ((P + k : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [e, e2]
    calc _ ≤ ((P : ℝ) ^ (-a) - ((P + k : ℕ) : ℝ) ^ (-a)) / a
          + (((P + k : ℕ) : ℝ) ^ (-a) - (((P + k : ℕ) : ℝ) + 1) ^ (-a)) / a := add_le_add ih h
      _ = _ := by ring

/-- Tail of the `p`-series: `∑_{n ≥ P+1} n^{-(a+1)} ≤ P^{-a} / a` for `a ≥ 1`. -/
lemma tsum_tail_rpow_le {a : ℝ} (ha : 1 ≤ a) (P : ℕ) (hP : 1 ≤ P) :
    Summable (fun n : ℕ => if P + 1 ≤ n then ((n : ℝ)) ^ (-(a + 1)) else 0) ∧
    ∑' n : ℕ, (if P + 1 ≤ n then ((n : ℝ)) ^ (-(a + 1)) else 0) ≤ (P : ℝ) ^ (-a) / a := by
  have hnn : ∀ n : ℕ, 0 ≤ (if P + 1 ≤ n then ((n : ℝ)) ^ (-(a + 1)) else 0) := by
    intro n; split_ifs <;> positivity
  have hb : ∀ M, ∑ n ∈ Finset.range M, (if P + 1 ≤ n then ((n : ℝ)) ^ (-(a + 1)) else 0)
      ≤ (P : ℝ) ^ (-a) / a := by
    intro M
    have h0 : 0 < a := by linarith
    calc _ ≤ ∑ n ∈ Finset.range (P + 1 + M),
            (if P + 1 ≤ n then ((n : ℝ)) ^ (-(a + 1)) else 0) :=
          Finset.sum_le_sum_of_subset_of_nonneg (by intro x; simp; omega) (fun i _ _ => hnn i)
      _ = ∑ n ∈ Finset.Ico (P + 1) (P + 1 + M), ((n : ℕ) : ℝ) ^ (-(a + 1)) := by
          rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (P+1)) (by omega)]
          rw [Finset.sum_eq_zero (fun i hi => by simp at hi; simp; omega), zero_add]
          exact Finset.sum_congr rfl (fun i hi => by simp at hi; simp [hi.1])
      _ ≤ ((P : ℝ) ^ (-a) - ((P + M : ℕ) : ℝ) ^ (-a)) / a := sum_Ico_rpow_le ha P hP M
      _ ≤ _ := by
          apply div_le_div_of_nonneg_right _ h0.le
          have : 0 ≤ ((P + M : ℕ) : ℝ) ^ (-a) := by positivity
          linarith
  exact ⟨summable_of_sum_range_le hnn hb, Real.tsum_le_of_sum_range_le hnn hb⟩

namespace Complex

/-- COMPLEX EULER PRODUCT (remainder over `ℂ`).
Ported from `/tmp/86f924db-58c6-4375-9ea5-2de8c76ce92e-aristotle.tar.gz`
`output-final_aristotle/zeta_handoff.lean` (Lean 4.34 adaptations: fold back
the unfolded `smoothNumbers` by `rfl`; `if_pos` → `ite_eq_left`). -/
theorem eulerprod_tail (s : ℂ) (hs : 2 ≤ s.re) (P : ℕ) (hP : 2 ≤ P) :
    ‖riemannZeta s - ∏ p ∈ Nat.primesBelow (P + 1), (1 - (p : ℂ) ^ (-s))⁻¹‖
      ≤ 2 / ((P : ℝ) ^ (s.re - 1) * (s.re - 1)) := by
  have hs1 : 1 < s.re := by linarith
  have hs0 : s ≠ 0 := ne_zero_of_one_lt_re hs1
  set F := riemannZetaSummandHom hs0 with hF
  have hFapp : ∀ n : ℕ, F n = (n : ℂ) ^ (-s) := fun n => rfl
  have hsum : Summable F := (summable_riemannZetaSummand hs1).of_norm
  have hζ : HasSum F (riemannZeta s) := by
    rw [← tsum_riemannZetaSummand hs1]; exact hsum.hasSum
  have hprod : ∏ p ∈ Nat.primesBelow (P + 1), (1 - (p : ℂ) ^ (-s))⁻¹
      = ∑' m : (P + 1).smoothNumbers, F m :=
    EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers
      (f := (F : ℕ →* ℂ)) hsum (P + 1)
  have hsub := hasSum_subtype_iff_indicator.mp (hsum.subtype ((P + 1).smoothNumbers)).hasSum
  have hdiff := hζ.sub hsub
  rw [hprod]
  set a := s.re - 1 with ha_def
  have ha : 1 ≤ a := by linarith
  obtain ⟨hgs, hgle⟩ := tsum_tail_rpow_le ha P (by omega)
  refine (hdiff.norm_le_of_bounded hgs.hasSum ?_).trans (hgle.trans ?_)
  · intro n
    -- 4.34 unfolds `smoothNumbers` in the `indicator` term; fold it back
    -- (defeq, so `rfl`) before the `indicator` rewrites.
    have hfold : (Set.indicator (fun x => x ≠ 0 ∧ ∀ p ∈ x.primeFactorsList, p < P + 1)
        (⇑F) n) = (Set.indicator ((P + 1).smoothNumbers) (⇑F) n) := rfl
    rw [hfold]
    by_cases hn : n ∈ (P + 1).smoothNumbers
    · simp [Set.indicator_of_mem hn]
      positivity
    · rw [Set.indicator_of_notMem hn, sub_zero, hFapp]
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · subst h0; simp [hs0]
      · have hle : P + 1 ≤ n := by
          by_contra h
          exact hn (Nat.mem_smoothNumbers_of_lt hpos (by omega))
        rw [ite_eq_left hle, Complex.norm_natCast_cpow_of_pos hpos]
        simp [ha_def]
  · rw [Real.rpow_neg (by positivity)]
    have hPpos : (0:ℝ) < (P : ℝ) ^ a := by
      apply Real.rpow_pos_of_pos; exact_mod_cast (by omega : 0 < P)
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    field_simp
    nlinarith

/-- info: '_private.Lynth.Interval.Fns.ComplexZeta.0.Complex.eulerprod_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.eulerprod_tail

/-- COMPLEX FUNCTIONAL EQUATION (solved for `ζ s`).
Ported from the same handoff (no adaptation needed). -/
theorem zeta_neg_fe (s : ℂ) (hs : s.re < 0) :
    riemannZeta s
      = ((((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1)) * Complex.sin ((Real.pi : ℂ) * s / 2))
        * Complex.Gamma (1 - s)) * riemannZeta (1 - s) := by
  have h1 : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := n.cast_nonneg
    linarith
  have h2 : (1 - s) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this; linarith
  have := riemannZeta_one_sub h1 h2
  rw [sub_sub_cancel] at this
  rw [this]
  have hc : Complex.cos (↑Real.pi * (1 - s) / 2) = Complex.sin (↑Real.pi * s / 2) := by
    rw [← Complex.cos_pi_div_two_sub]; congr 1; ring
  have hp : (2 * (Real.pi : ℂ)) ^ (-(1 - s)) = (2:ℂ) ^ (s - 1) * (Real.pi : ℂ) ^ (s - 1) := by
    rw [neg_sub]
    have := Complex.mul_cpow_ofReal_nonneg (by norm_num : (0:ℝ) ≤ 2) Real.pi_pos.le (s - 1)
    simpa using this
  have h2s : (2:ℂ) * (2:ℂ) ^ (s - 1) = (2:ℂ) ^ s := by
    rw [Complex.cpow_sub _ _ (by norm_num), Complex.cpow_one]
    field_simp
  rw [hc, hp, ← h2s]
  ring

/-- info: '_private.Lynth.Interval.Fns.ComplexZeta.0.Complex.zeta_neg_fe' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Complex.zeta_neg_fe

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Euler product -/

/-- fold `CBox.mul` over interval factors. -/
@[expose] public def cprodC (w : Nat) : List CBox → CBox
  | [] => oneCBox
  | B :: Bs => CBox.mul w B (cprodC w Bs)

theorem mem_cprodC (w : Nat) (xs : List ℂ) (Bs : List CBox)
    (h : List.Forall₂ (fun x B => x ∈ B) xs Bs) :
    xs.prod ∈ cprodC w Bs := by
  induction h with
  | nil => simpa [cprodC] using mem_oneCBox
  | cons hx _ ih =>
    simp only [cprodC, List.prod_cons]
    exact CBox.mem_mul hx ih

/-- one Euler factor value `1/(1 - p⁻ˢ)` (inverse form, matching the handoff). -/
noncomputable def eulerFactorVal (s : ℂ) (p : Nat) : ℂ := (1 - (p : ℂ) ^ (-s))⁻¹

/-- one Euler factor box. -/
@[expose] public def eulerFactorC (c : Ctx) (S : CBox) (p : Nat) : CBox :=
  let w := c.prec + 16
  CBox.div w oneCBox
    (CBox.sub w oneCBox
      (expBox c (CBox.mul c.prec (logBox c (CBox.ofReal (Ival.ofRat w (p : ℚ))))
        (CBox.neg S))))

theorem mem_eulerFactorC {c : Ctx} (hc : c.Valid) {s : ℂ} {S : CBox} (hx : s ∈ S)
    (p : Nat) (hp : p.Prime) :
    eulerFactorVal s p ∈ eulerFactorC c S p := by
  have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hp.pos)
  have hcpow : ((p : ℕ) : ℂ) ^ (-s)
      ∈ expBox c (CBox.mul c.prec
        (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (p : ℚ)))) (CBox.neg S)) :=
    mem_cpow_point hc (natCastC_mem_ofRat _ p) hp0 (CBox.mem_neg hx)
  unfold eulerFactorC eulerFactorVal
  simp only
  rw [← one_div]
  exact CBox.mem_div mem_oneCBox (CBox.mem_sub mem_oneCBox hcpow)

/-- handoff product (`primesBelow`) is the evaluator product (`eulerPrimes`). -/
theorem eulerProdC_eq (s : ℂ) (P : Nat) :
    ∏ p ∈ Nat.primesBelow (P + 1), (1 - (p : ℂ) ^ (-s))⁻¹
      = ((eulerPrimes P).map fun p => eulerFactorVal s p).prod := by
  rw [Finset.prod_eq_multiset_prod]
  have h : (Nat.primesBelow (P + 1)).val = (eulerPrimes P : Multiset ℕ) := by
    simp [Nat.primesBelow, eulerPrimes, Finset.filter_val, Finset.range_val, Multiset.range]
  rw [h, Multiset.map_coe, Multiset.prod_coe]
  rfl

/-- interval tail bound `2/(P^{σ-1}·(σ-1))` over the `Re` enclosure. -/
@[expose] public def zetaTailC (c : Ctx) (S : CBox) (P : Nat) : Ival :=
  let w := c.prec + 16
  let sigM1 := Ival.sub w S.re (Ival.ofRat w 1)
  let pw := rpowIval c (Ival.ofRat w (P : ℚ)) sigM1
  Ival.div w (Ival.ofRat w 2) (Ival.mul w pw sigM1)

theorem mem_zetaTailC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox} (hx : z ∈ S)
    (P : Nat) :
    2 / ((P : ℝ) ^ (z.re - 1) * (z.re - 1)) ∈ zetaTailC c S P := by
  unfold zetaTailC
  simp only
  have h1m : ((1 : ℚ) : ℝ) ∈ Ival.ofRat (c.prec + 16) (1 : ℚ) := Ival.mem_ofRat _ _
  have e1 : ((1 : ℚ) : ℝ) = 1 := by simp
  rw [e1] at h1m
  have h2m : ((2 : ℚ) : ℝ) ∈ Ival.ofRat (c.prec + 16) (2 : ℚ) := Ival.mem_ofRat _ _
  have e2 : ((2 : ℚ) : ℝ) = 2 := by simp
  rw [e2] at h2m
  have hP : (((P : ℕ)) : ℝ) ∈ Ival.ofRat (c.prec + 16) (P : ℚ) := by
    have h := Ival.mem_ofRat (c.prec + 16) (P : ℚ)
    rwa [Rat.cast_natCast] at h
  have hsig : z.re - 1
      ∈ Ival.sub (c.prec + 16) S.re (Ival.ofRat (c.prec + 16) (1 : ℚ)) :=
    Ival.mem_sub hx.1 h1m
  have hpw : ((P : ℕ) : ℝ) ^ (z.re - 1)
      ∈ rpowIval c (Ival.ofRat (c.prec + 16) (P : ℚ))
        (Ival.sub (c.prec + 16) S.re (Ival.ofRat (c.prec + 16) (1 : ℚ))) :=
    mem_rpowIval hc hP hsig
  exact Ival.mem_div h2m (Ival.mem_mul hpw hsig)

/-- Euler-product enclosure at cutoff `P`. -/
@[expose] public def zetaEulerProdC (c : Ctx) (S : CBox) (P : Nat) : CBox :=
  let w := c.prec + 16
  let prod := cprodC w ((eulerPrimes P).map (eulerFactorC c S))
  widenCBox w prod (Ival.magHi (zetaTailC c S P))

theorem mem_zetaEulerProdC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox} {P : Nat}
    (hx : z ∈ S) (h2 : 2 ≤ z.re) (hP : 2 ≤ P) :
    riemannZeta z ∈ zetaEulerProdC c S P := by
  have htail := Complex.eulerprod_tail z h2 P hP
  rw [eulerProdC_eq] at htail
  have hmap : List.Forall₂ (fun x B => x ∈ B)
      ((eulerPrimes P).map fun p => eulerFactorVal z p)
      ((eulerPrimes P).map (eulerFactorC c S)) := by
    suffices h : ∀ ps : List Nat, (∀ p ∈ ps, p.Prime) → List.Forall₂ (fun x B => x ∈ B)
        (ps.map fun p => eulerFactorVal z p) (ps.map (eulerFactorC c S)) by
      exact h _ (fun p hp => (eulerPrimes_mem.mp hp).1)
    intro ps hmem
    induction ps with
    | nil => exact List.Forall₂.nil
    | cons p ps ih =>
      have hp : p.Prime := hmem p (by simp)
      refine List.Forall₂.cons (mem_eulerFactorC hc hx p hp)
        (ih fun q hq => hmem q ?_)
      exact List.mem_cons_of_mem p hq
  have hprod : ((eulerPrimes P).map fun p => eulerFactorVal z p).prod
      ∈ cprodC (c.prec + 16) ((eulerPrimes P).map (eulerFactorC c S)) :=
    mem_cprodC _ _ _ hmap
  have hT : 2 / ((P : ℝ) ^ (z.re - 1) * (z.re - 1))
      ∈ zetaTailC c S P := mem_zetaTailC (c := c) hc hx P
  unfold zetaEulerProdC
  simp only
  apply mem_widenCBox hprod
  intro m hm
  have hB : 2 / ((P : ℝ) ^ (z.re - 1) * (z.re - 1)) ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  exact le_trans htail hB

/-! ### Closed form `ζ(2) = π²/6` (point boxes) -/

/-- `π²/6` box. -/
@[expose] public def closedTwoC (c : Ctx) : CBox :=
  let w := c.prec + 16
  CBox.div w (CBox.npow w (CBox.ofReal c.pi) 2) (sixC w)

theorem mem_closedTwoC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox}
    (hx : z ∈ S) {lo hi ilo ihi : Dy}
    (hlo : S.re.lo = some lo) (hhi : S.re.hi = some hi)
    (hilo : S.im.lo = some ilo) (hihi : S.im.hi = some ihi)
    (h2 : lo.toRat = 2 ∧ hi.toRat = 2 ∧ ilo.toRat = 0 ∧ ihi.toRat = 0) :
    riemannZeta z ∈ closedTwoC c := by
  have hre : z.re = 2 := by
    have h1 := mem_lo_le hx.1 hlo
    have h2l := mem_le_hi hx.1 hhi
    rw [h2.1] at h1
    rw [h2.2.1] at h2l
    simp only [Rat.cast_ofNat] at h1 h2l
    exact le_antisymm h2l h1
  have him : z.im = 0 := by
    have h1 := mem_lo_le hx.2 hilo
    have h2l := mem_le_hi hx.2 hihi
    rw [h2.2.2.1] at h1
    rw [h2.2.2.2] at h2l
    simp only [Rat.cast_zero] at h1 h2l
    exact le_antisymm h2l h1
  have ez : z = ((2 : ℕ) : ℂ) := by
    apply Complex.ext <;> simp [hre, him]
  have e2 : ((2 : ℕ) : ℂ) = (2 : ℂ) := by norm_num
  rw [ez, e2, riemannZeta_two]
  exact CBox.mem_div (CBox.mem_npow (CBox.mem_ofReal hc.pi_mem) 2) (mem_sixC)

/-! ### Positive dispatch (`Re ≥ 2`) -/

/-- `ζ` on boxes with `Re ≥ 2`: point `2` → closed form, `Re ≥ 6` →
Euler product (fast tail), else Euler–Maclaurin (the Euler tail at
`σ < 6` is too wide to be useful). -/
@[expose] public def zetaPosC (c : Ctx) (S : CBox) : CBox :=
  let w := c.prec + 16
  match S.re.lo, S.re.hi, S.im.lo, S.im.hi with
  | some lo, some hi, some ilo, some ihi =>
    if lo.toRat = 2 ∧ hi.toRat = 2 ∧ ilo.toRat = 0 ∧ ihi.toRat = 0 then closedTwoC c
    else if 6 ≤ lo.toRat then zetaEulerProdC c S (64 + 2 * c.prec)
    else if 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat) then zetaEMGuardC c S lo hi
    else CBox.top
  | _, _, _, _ => CBox.top

theorem mem_zetaPosC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox}
    (hx : z ∈ S) :
    riemannZeta z ∈ zetaPosC c S := by
  cases hlo : S.re.lo with
  | none =>
    cases hhi : S.re.hi with
    | none =>
      cases hloi : S.im.lo with
      | none =>
        cases hhii : S.im.hi with
        | none =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some _ =>
        have hev : zetaPosC c S = CBox.top := by
          simp [zetaPosC, hlo, hhi, hloi]
        rw [hev]; exact CBox.mem_top _
    | some _ =>
      have hev : zetaPosC c S = CBox.top := by
        simp [zetaPosC, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
  | some lo =>
    cases hhi : S.re.hi with
    | none =>
      cases hloi : S.im.lo with
      | none =>
        cases hhii : S.im.hi with
        | none =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some _ =>
        have hev : zetaPosC c S = CBox.top := by
          simp [zetaPosC, hlo, hhi, hloi]
        rw [hev]; exact CBox.mem_top _
    | some hi =>
      cases hloi : S.im.lo with
      | none =>
        cases hhii : S.im.hi with
        | none =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some ilo =>
        cases hhii : S.im.hi with
        | none =>
          have hev : zetaPosC c S = CBox.top := by
            simp [zetaPosC, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some ihi =>
          by_cases hpt : lo.toRat = 2 ∧ hi.toRat = 2 ∧ ilo.toRat = 0 ∧ ihi.toRat = 0
          · have hev : zetaPosC c S = closedTwoC c := by
              simp [zetaPosC, hlo, hhi, hloi, hhii, eq_true hpt]
            rw [hev]
            exact mem_closedTwoC hc hx hlo hhi hloi hhii hpt
          · by_cases hge : 6 ≤ lo.toRat
            · have hev : zetaPosC c S = zetaEulerProdC c S (64 + 2 * c.prec) := by
                simp [zetaPosC, hlo, hhi, hloi, hhii, hpt, eq_true hge]
              rw [hev]
              have hre : 2 ≤ z.re := by
                have h1 := mem_lo_le hx.1 hlo
                have h2l : (6 : ℝ) ≤ ((lo.toRat : ℚ) : ℝ) := by
                  exact_mod_cast hge
                linarith
              exact mem_zetaEulerProdC hc hx hre (by omega)
            · by_cases hem : 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat)
              · have hev : zetaPosC c S = zetaEMGuardC c S lo hi := by
                  simp [zetaPosC, hlo, hhi, hloi, hhii, hpt, hge, eq_true hem]
                rw [hev]
                exact mem_zetaEMGuardC hc hx hlo hhi
              · have hev : zetaPosC c S = CBox.top := by
                  simp [zetaPosC, hlo, hhi, hloi, hhii, hpt, hge, hem]
                rw [hev]
                exact CBox.mem_top _

/-- inner values (`Re > 1` always here): Euler product at `Re ≥ 2`,
Euler–Maclaurin on `(1, 2)`. (Non-recursive: the outer `Re < 0` rules out
a second reflection.) -/
@[expose] public def zetaInnerC (c : Ctx) (Y : CBox) : CBox :=
  match Y.re.lo, Y.re.hi with
  | some lo, some hi =>
    if 2 ≤ lo.toRat then zetaPosC c Y
    else if 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat) then zetaEMGuardC c Y lo hi
    else CBox.top
  | _, _ => CBox.top

theorem mem_zetaInnerC {c : Ctx} (hc : c.Valid) {z : ℂ} {Y : CBox}
    (hx : z ∈ Y) : riemannZeta z ∈ zetaInnerC c Y := by
  cases hlo : Y.re.lo with
  | none =>
    cases hhi : Y.re.hi with
    | none =>
      have hev : zetaInnerC c Y = CBox.top := by simp [zetaInnerC, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
    | some _ =>
      have hev : zetaInnerC c Y = CBox.top := by simp [zetaInnerC, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
  | some lo =>
    cases hhi : Y.re.hi with
    | none =>
      have hev : zetaInnerC c Y = CBox.top := by simp [zetaInnerC, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
    | some hi =>
      by_cases hge : 2 ≤ lo.toRat
      · have hev : zetaInnerC c Y = zetaPosC c Y := by
          simp [zetaInnerC, hlo, hhi, eq_true hge]
        rw [hev]; exact mem_zetaPosC hc hx
      · by_cases hem : 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat)
        · have hev : zetaInnerC c Y = zetaEMGuardC c Y lo hi := by
            simp [zetaInnerC, hlo, hhi, hge, eq_true hem]
          rw [hev]; exact mem_zetaEMGuardC hc hx hlo hhi
        · have hev : zetaInnerC c Y = CBox.top := by
            simp [zetaInnerC, hlo, hhi, hge, hem]
          rw [hev]; exact CBox.mem_top _

/-! ### Reflection (`Re < 0`) -/

/-- `ζ` via `ζ(s) = 2^s·π^{s-1}·sin(πs/2)·Γ(1-s)·ζ(1-s)`. -/
@[expose] public def zetaNegC (c : Ctx) (X : CBox) : CBox :=
  let w := c.prec + 16
  let A := expBox c (CBox.mul c.prec (logBox c (twoC w)) X)
  let B := expBox c (CBox.mul c.prec (logBox c (CBox.ofReal c.pi))
    (CBox.sub w X (CBox.ofReal Ival.one)))
  let C := sinBox c (CBox.div w (CBox.mul w (CBox.ofReal c.pi) X) (twoC w))
  let D := gammaCBox c (CBox.sub w (CBox.ofReal Ival.one) X)
  let E := zetaInnerC c (CBox.sub w (CBox.ofReal Ival.one) X)
  CBox.mul w (CBox.mul w (CBox.mul w (CBox.mul w A B) C) D) E

theorem mem_zetaNegC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) (hle : z.re < 0) :
    riemannZeta z ∈ zetaNegC c X := by
  have hFE := Complex.zeta_neg_fe z hle
  have hA : (2 : ℂ) ^ z
      ∈ expBox c (CBox.mul c.prec (logBox c (twoC (c.prec + 16))) X) :=
    mem_cpow_point hc (mem_twoC) (by norm_num) hx
  have hpi : (Real.pi : ℂ) ∈ CBox.ofReal c.pi := CBox.mem_ofReal hc.pi_mem
  have hpi0 : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hB : (Real.pi : ℂ) ^ (z - 1)
      ∈ expBox c (CBox.mul c.prec (logBox c (CBox.ofReal c.pi))
        (CBox.sub (c.prec + 16) X (CBox.ofReal Ival.one))) :=
    mem_cpow_point hc hpi hpi0 (CBox.mem_sub hx (mem_oneC))
  have hC : Complex.sin ((Real.pi : ℂ) * z / 2)
      ∈ sinBox c (CBox.div (c.prec + 16)
        (CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X) (twoC (c.prec + 16))) :=
    mem_sinBox c hc (CBox.mem_div (CBox.mem_mul hpi hx) (mem_twoC))
  have hD : Complex.Gamma (1 - z)
      ∈ gammaCBox c (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X) :=
    mem_gammaCBox hc (CBox.mem_sub (mem_oneC) hx)
  have hE : riemannZeta (1 - z)
      ∈ zetaInnerC c (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X) :=
    mem_zetaInnerC hc (CBox.mem_sub (mem_oneC) hx)
  unfold zetaNegC
  simp only
  rw [hFE]
  exact CBox.mem_mul (CBox.mem_mul (CBox.mem_mul (CBox.mem_mul hA hB) hC) hD) hE

/-! ### Top-level dispatch -/

/-- `ζ` on any box: Euler product at `Re ≥ 2`, reflection at `Re < 0`,
Euler–Maclaurin at `0 < Re ≠ 1`, `⊤` elsewhere (poles, `Re = 0`). -/
@[expose] public def zetaCBox (c : Ctx) (X : CBox) : CBox :=
  match X.re.lo, X.re.hi with
  | some lo, some hi =>
    if 2 ≤ lo.toRat then zetaPosC c X
    else if hi.toRat < 0 then zetaNegC c X
    else match X.im.lo, X.im.hi with
      | some ilo, some ihi =>
        if 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat) then
          zetaEMGuardC c X lo hi
        else CBox.top
      | _, _ => CBox.top
  | _, _ => CBox.top

theorem mem_zetaCBox {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) : riemannZeta z ∈ zetaCBox c X := by
  cases hlo : X.re.lo with
  | none =>
    cases hhi : X.re.hi with
    | none =>
      have hev : zetaCBox c X = CBox.top := by simp [zetaCBox, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
    | some _ =>
      have hev : zetaCBox c X = CBox.top := by simp [zetaCBox, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
  | some lo =>
    cases hhi : X.re.hi with
    | none =>
      have hev : zetaCBox c X = CBox.top := by simp [zetaCBox, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
    | some hi =>
      by_cases hge : 2 ≤ lo.toRat
      · have hev : zetaCBox c X = zetaPosC c X := by
          simp [zetaCBox, hlo, hhi, eq_true hge]
        rw [hev]; exact mem_zetaPosC hc hx
      · by_cases hneg : hi.toRat < 0
        · have hev : zetaCBox c X = zetaNegC c X := by
            simp [zetaCBox, hlo, hhi, hge, eq_true hneg]
          rw [hev]
          have hleR : z.re < 0 := by
            have h1 := mem_le_hi hx.1 hhi
            have h2 : ((hi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
            linarith
          exact mem_zetaNegC hc hx hleR
        · cases hilo : X.im.lo with
          | none =>
            cases hhii : X.im.hi with
            | none =>
              have hev : zetaCBox c X = CBox.top := by
                simp [zetaCBox, hlo, hhi, hge, hneg, hilo, hhii]
              rw [hev]; exact CBox.mem_top _
            | some _ =>
              have hev : zetaCBox c X = CBox.top := by
                simp [zetaCBox, hlo, hhi, hge, hneg, hilo, hhii]
              rw [hev]; exact CBox.mem_top _
          | some ilo =>
            cases hhii : X.im.hi with
            | none =>
              have hev : zetaCBox c X = CBox.top := by
                simp [zetaCBox, hlo, hhi, hge, hneg, hilo, hhii]
              rw [hev]; exact CBox.mem_top _
            | some ihi =>
              by_cases hem : 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat)
              · have hev : zetaCBox c X = zetaEMGuardC c X lo hi := by
                  simp [zetaCBox, hlo, hhi, hge, hneg, hilo, hhii, eq_true hem]
                rw [hev]
                exact mem_zetaEMGuardC hc hx hlo hhi
              · have hev : zetaCBox c X = CBox.top := by
                  simp [zetaCBox, hlo, hhi, hge, hneg, hilo, hhii, hem]
                rw [hev]; exact CBox.mem_top _

@[expose, lynth_cfn] public def zetaC : Fn1 .cplx .cplx where
  name := "riemannZeta"
  graph x y := y = riemannZeta x
  exu := by exact exu_eq _
  ev := zetaCBox
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_zetaCBox hc hx
  cost := 500

end Lynth.Interval.Fns
