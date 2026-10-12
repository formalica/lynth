import Lynth.Interval.Fns.Zeta
import Lynth.Interval.Fns.ComplexGamma
import Lynth.Interval.Fns.ComplexElem

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
functional equation solved for `ζ s` — are stated below as mirrors of
`/tmp/complex/zeta_handoff.lean` (same contract as the Stirling mirror:
keep byte-identical, paste the prover's proof back).  Everything else is
proved inline.  The strip `(-1, 2)` (critical strip, `ζ(1/2)`, `ζ(3/2)`,
`ζ(-1/2)`, `ζ(3)`, `ζ(5)`, …) needs complex Euler–Maclaurin and is left for
the next batch.
-/

namespace Complex

/-- COMPLEX EULER PRODUCT (remainder over `ℂ`).
Mirror of `/tmp/complex/zeta_handoff.lean` for the external prover. -/
theorem eulerprod_tail (s : ℂ) (hs : 2 ≤ s.re) (P : ℕ) (hP : 2 ≤ P) :
    ‖riemannZeta s - ∏ p ∈ Nat.primesBelow (P + 1), (1 - (p : ℂ) ^ (-s))⁻¹‖
      ≤ 2 / ((P : ℝ) ^ (s.re - 1) * (s.re - 1)) := by
  sorry

/-- COMPLEX FUNCTIONAL EQUATION (solved for `ζ s`).
Mirror of `/tmp/complex/zeta_handoff.lean` for the external prover. -/
theorem zeta_neg_fe (s : ℂ) (hs : s.re < 0) :
    riemannZeta s
      = ((((2 : ℂ) ^ s * (Real.pi : ℂ) ^ (s - 1)) * Complex.sin ((Real.pi : ℂ) * s / 2))
        * Complex.Gamma (1 - s)) * riemannZeta (1 - s) := by
  sorry

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Small constant boxes -/

/-- the constant `2` box. -/
def twoC (w : Nat) : CBox := CBox.ofReal (Ival.ofRat w 2)

theorem mem_twoC {w : Nat} : (2 : ℂ) ∈ twoC w := by
  rw [twoC]
  simpa using CBox.mem_ofReal (Ival.mem_ofRat w (2 : ℚ))

/-- the constant `6` box. -/
def sixC (w : Nat) : CBox := CBox.ofReal (Ival.ofRat w 6)

theorem mem_sixC {w : Nat} : (6 : ℂ) ∈ sixC w := by
  rw [sixC]
  simpa using CBox.mem_ofReal (Ival.mem_ofRat w (6 : ℚ))

/-- the constant `1` box. -/
def oneCBox : CBox := ⟨Ival.one, Ival.zero⟩

theorem mem_oneCBox : (1 : ℂ) ∈ oneCBox :=
  ⟨by rw [Complex.one_re]; exact Ival.mem_one,
   by rw [Complex.one_im]; exact Ival.mem_zero⟩

theorem mem_oneC : (1 : ℂ) ∈ CBox.ofReal Ival.one := by
  rw [← Complex.ofReal_one]
  exact CBox.mem_ofReal Ival.mem_one

/-- `cpow` with a known-nonzero constant base, via `exp`/`log`. -/
theorem mem_cpow_point {c : Ctx} (hc : c.Valid) {b : ℂ} {B : CBox} {y : ℂ} {Y : CBox}
    (hb : b ∈ B) (hb0 : b ≠ 0) (hy : y ∈ Y) :
    b ^ y ∈ expBox c (CBox.mul c.prec (logBox c B) Y) := by
  rw [Complex.cpow_def, ite_eq_right hb0]
  exact mem_expBox c hc (CBox.mem_mul (mem_logBox c hc hb) hy)

/-! ### Euler product -/

/-- fold `CBox.mul` over interval factors. -/
def cprodC (w : Nat) : List CBox → CBox
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
def eulerFactorC (c : Ctx) (S : CBox) (p : Nat) : CBox :=
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
def zetaTailC (c : Ctx) (S : CBox) (P : Nat) : Ival :=
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
def zetaEulerProdC (c : Ctx) (S : CBox) (P : Nat) : CBox :=
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
def closedTwoC (c : Ctx) : CBox :=
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

/-- `ζ` on boxes with `Re ≥ 2`: point `2` → closed form, else Euler product. -/
def zetaPosC (c : Ctx) (S : CBox) : CBox :=
  let w := c.prec + 16
  match S.re.lo, S.re.hi, S.im.lo, S.im.hi with
  | some lo, some hi, some ilo, some ihi =>
    if lo.toRat = 2 ∧ hi.toRat = 2 ∧ ilo.toRat = 0 ∧ ihi.toRat = 0 then closedTwoC c
    else if 2 ≤ lo.toRat then zetaEulerProdC c S (64 + 2 * c.prec)
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
          · by_cases hge : 2 ≤ lo.toRat
            · have hev : zetaPosC c S = zetaEulerProdC c S (64 + 2 * c.prec) := by
                simp [zetaPosC, hlo, hhi, hloi, hhii, hpt, eq_true hge]
              rw [hev]
              have hre : 2 ≤ z.re := by
                have h1 := mem_lo_le hx.1 hlo
                have h2l : (2 : ℝ) ≤ ((lo.toRat : ℚ) : ℝ) := by
                  exact_mod_cast hge
                linarith
              exact mem_zetaEulerProdC hc hx hre (by omega)
            · have hev : zetaPosC c S = CBox.top := by
                simp [zetaPosC, hlo, hhi, hloi, hhii, hpt, hge]
              rw [hev]
              exact CBox.mem_top _

/-! ### Reflection (`Re ≤ -1`) -/

/-- `ζ` via `ζ(s) = 2^s·π^{s-1}·sin(πs/2)·Γ(1-s)·ζ(1-s)`. -/
def zetaNegC (c : Ctx) (X : CBox) : CBox :=
  let w := c.prec + 16
  let A := expBox c (CBox.mul c.prec (logBox c (twoC w)) X)
  let B := expBox c (CBox.mul c.prec (logBox c (CBox.ofReal c.pi))
    (CBox.sub w X (CBox.ofReal Ival.one)))
  let C := sinBox c (CBox.div w (CBox.mul w (CBox.ofReal c.pi) X) (twoC w))
  let D := gammaCBox c (CBox.sub w (CBox.ofReal Ival.one) X)
  let E := zetaPosC c (CBox.sub w (CBox.ofReal Ival.one) X)
  CBox.mul w (CBox.mul w (CBox.mul w (CBox.mul w A B) C) D) E

theorem mem_zetaNegC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) (hle : z.re ≤ -1) :
    riemannZeta z ∈ zetaNegC c X := by
  have hFE := Complex.zeta_neg_fe z (by linarith : z.re < 0)
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
      ∈ zetaPosC c (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X) :=
    mem_zetaPosC hc (CBox.mem_sub (mem_oneC) hx)
  unfold zetaNegC
  simp only
  rw [hFE]
  exact CBox.mem_mul (CBox.mem_mul (CBox.mem_mul (CBox.mem_mul hA hB) hC) hD) hE

/-! ### Top-level dispatch -/

/-- `ζ` on any box: Euler product at `Re ≥ 2`, reflection at `Re ≤ -1`,
`⊤` on the strip (complex Euler–Maclaurin is a later batch). -/
def zetaCBox (c : Ctx) (X : CBox) : CBox :=
  match X.re.lo, X.re.hi with
  | some lo, some hi =>
    if 2 ≤ lo.toRat then zetaPosC c X
    else if hi.toRat ≤ -1 then zetaNegC c X
    else CBox.top
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
      · by_cases hle : hi.toRat ≤ -1
        · have hev : zetaCBox c X = zetaNegC c X := by
            simp [zetaCBox, hlo, hhi, hge, eq_true hle]
          rw [hev]
          have hleR : z.re ≤ -1 := by
            have h1 := mem_le_hi hx.1 hhi
            have h2 : ((hi.toRat : ℚ) : ℝ) ≤ -1 := by exact_mod_cast hle
            linarith
          exact mem_zetaNegC hc hx hleR
        · have hev : zetaCBox c X = CBox.top := by
            simp [zetaCBox, hlo, hhi, hge, hle]
          rw [hev]; exact CBox.mem_top _

@[lynth_cfn] def zetaC : Fn1 .cplx .cplx where
  name := "riemannZeta"
  graph x y := y = riemannZeta x
  exu := exu_eq _
  ev := zetaCBox
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_zetaCBox hc hx
  cost := 500

end Lynth.Interval.Fns
