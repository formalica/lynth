import Lynth.Interval.Fns.EMCore.Digamma
import Lynth.Interval.Fns.Digamma
import Lynth.Interval.Fns.ComplexGamma
import Lynth.Interval.Fns.ComplexZeta
import Lynth.Interval.Fns.ComplexElem

/-!
# Complex digamma via shift + Stirling (`Re > 0`) and reflection.

Mirror of `Lynth/Interval/Fns/Digamma.lean` with `Ival` replaced by `CBox`
and `|·|` by `‖·‖`: argument shifting with
`ψ(s+n) = ψ(s) + Σ_{k<n} 1/(s+k)` (`Complex.digamma_apply_add_nat`) until
`Re ≥ X₀`, Stirling expansion of `ψ` with explicit remainder, then subtract
the shift sum.  Negative arguments go through reflection
`ψ(s) = ψ(1-s) - π·cot(πs)` (`Complex.digamma_one_sub`); boxes meeting a
pole (`-m`, `m : ℕ`) go to `⊤`.

The one analytic input — the corrected complex Stirling expansion
(`Complex.dig_stirling_bound_sector`, sector-factor remainder) — is ported
from `/tmp/complex2/digamma_handoff.lean` (the original factor-2 statement
is believed false).  Shift, reflection and pole avoidance are proved
inline from Mathlib facts.  The strip around `Re = 0` goes to `⊤`.
-/

namespace Complex

/-- COMPLEX STIRLING for digamma — corrected (sector factor).
Ported from `/tmp/complex2/digamma_handoff.lean` (Lean 4.28 → 4.34); the original
factor-2 statement is believed FALSE (numerical evidence in the handoff).

Changes w.r.t. the original:
* the remainder bound carries the factor `(2‖w‖ / (‖w‖ + Re w)) ^ (K + 2)`
  (a bound for `sec^{2K+3}(arg w / 2)`), which equals `1` for real `w`;
* the hypothesis `8 ≤ w.re` is weakened to `0 < w.re`, and `1 ≤ K` is dropped (unused).

The remainder is the Euler–Maclaurin tail `∑_{k ≥ 0} ∫_k^{k+1} (B_{2K+2}(x-k) - B_{2K+2})/(2K+2)! ·
d^{2K+2}/dx^{2K+2} (x + w)⁻¹ dx`. -/
theorem dig_stirling_bound_sector (w : ℂ) (hw : 0 < w.re) (K : ℕ) :
    ∃ R : ℂ, Complex.digamma w
        = Complex.log w - 1 / (2 * w)
          + (∑ k ∈ Finset.range K,
              -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * w ^ (2 * (k + 1)))) + R
      ∧ ‖R‖ ≤ (2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ)))))
          * (2 * ‖w‖ / (‖w‖ + w.re)) ^ (K + 2) / ‖w‖ ^ (2 * (K + 1)) := by
  refine ⟨EMCore.digR w (K + 1), ?_, ?_⟩
  · have := EMCore.digamma_eq_stirling hw (N := K + 1) (by omega)
    simpa using this
  · exact EMCore.digR_bound hw (N := K + 1) (by omega)

/-- info: 'Complex.dig_stirling_bound_sector' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Complex.dig_stirling_bound_sector

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Shift identity (inline from `digamma_apply_add_nat`) -/

/-- `ψ(x) = ψ(x+n) - Σ_{k<n} 1/(x+k)` for pole-free `x`. -/
theorem digamma_shiftC {x : ℂ} (hx : ∀ m : ℕ, x ≠ -((m : ℕ) : ℂ)) (n : Nat) :
    Complex.digamma x
      = Complex.digamma (x + (n : ℂ)) - ∑ k ∈ Finset.range n, (x + (k : ℂ))⁻¹ := by
  have h := Complex.digamma_apply_add_nat hx n
  rw [h]
  ring

/-! ### Pole gate -/

/-- box meets a pole `-m`: nonpos integer in `Re` range and `0` in `Im`. -/
def digHasPoleC (relo rehi ilo ihi : Dy) : Bool :=
  decide (⌈relo.toRat⌉ ≤ ⌊rehi.toRat⌋ ∧ ⌈relo.toRat⌉ ≤ 0 ∧ ilo.toRat ≤ 0 ∧ 0 ≤ ihi.toRat)

/-- a negative pole test rules out every `z = -m`. -/
theorem digHasPoleC_false {relo rehi ilo ihi : Dy}
    (h : digHasPoleC relo rehi ilo ihi = false) {z : ℂ}
    (hxr1 : ((relo.toRat : ℚ) : ℝ) ≤ z.re) (hxr2 : z.re ≤ ((rehi.toRat : ℚ) : ℝ))
    (hxi1 : ((ilo.toRat : ℚ) : ℝ) ≤ z.im) (hxi2 : z.im ≤ ((ihi.toRat : ℚ) : ℝ))
    (m : Nat) : z ≠ -(((m : ℕ)) : ℂ) := by
  intro he
  have hre : z.re = (-(m : ℝ)) := by
    have hr := congrArg Complex.re he
    simpa using hr
  have him : z.im = 0 := by
    have hi := congrArg Complex.im he
    simpa using hi
  have e : ((-(m : ℤ) : ℚ) : ℝ) = (-(m : ℝ)) := by push_cast; ring
  have e1 : relo.toRat ≤ (-(m : ℤ) : ℚ) := by
    have h' : ((relo.toRat : ℚ) : ℝ) ≤ ((-(m : ℤ) : ℚ) : ℝ) := by
      rw [e]
      exact hxr1.trans hre.le
    exact_mod_cast h'
  have e2 : (-(m : ℤ) : ℚ) ≤ rehi.toRat := by
    have h' : ((-(m : ℤ) : ℚ) : ℝ) ≤ ((rehi.toRat : ℚ) : ℝ) := by
      rw [e]
      exact (hre.symm.le).trans hxr2
    exact_mod_cast h'
  have c1 : ⌈relo.toRat⌉ ≤ -(m : ℤ) := Int.ceil_le.mpr e1
  have c2 : -(m : ℤ) ≤ ⌊rehi.toRat⌋ := Int.le_floor.mpr e2
  have c3 : ⌈relo.toRat⌉ ≤ 0 := le_trans c1 (by omega)
  have c4 : ilo.toRat ≤ 0 := by
    have h' : ((ilo.toRat : ℚ) : ℝ) ≤ 0 := by
      rw [← him]
      exact hxi1
    exact_mod_cast h'
  have c5 : (0 : ℚ) ≤ ihi.toRat := by
    have h' : (0 : ℝ) ≤ ((ihi.toRat : ℚ) : ℝ) := by
      rw [← him]
      exact hxi2
    exact_mod_cast h'
  have h' := of_decide_eq_false h
  exact h' ⟨le_trans c1 c2, c3, c4, c5⟩

/-! ### Stirling corrections -/

/-- one correction box `Q/Y^{2j}`. -/
def digCorrBoxC (c : Ctx) (Q : ℚ) (Y : CBox) (j : Nat) : CBox :=
  CBox.div (c.prec + 16) (CBox.ofReal (Ival.ofRat (c.prec + 16) Q))
    (CBox.npow (c.prec + 16) Y (2 * j))

/-- Stirling enclosure at `Y ∋ w` (log, half term, `K` corrections from the
Bernoulli list `L`, widened by the interval tail). -/
def digStirlingC (c : Ctx) (Y : CBox) (L : List ℚ) (K : Nat) : CBox :=
  let w := c.prec + 16
  let logT := logBox c Y
  let halfT := CBox.div w oneCBox (CBox.mul w (twoC w) Y)
  let corrs : List CBox := (List.range K).map fun k =>
    digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)
  let sumPart := csumC w ([logT, CBox.neg halfT] ++ corrs)
  let tail := Ival.mul w
    (Ival.div w
      (Ival.ofRat w (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))))
      (Ival.npow w (CBox.norm w Y) (2 * (K + 1))))
    (secFactorC w Y (K + 2))
  widenCBox w sumPart (Ival.magHi tail)

/-- the corrected tail bound, reassociated for the interval tail. -/
theorem dig_tail_bridge (K : ℕ) (z : ℂ) :
    (2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ)))))
      * (2 * ‖z‖ / (‖z‖ + z.re)) ^ (K + 2) / ‖z‖ ^ (2 * (K + 1))
      = ((2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ))))) / ‖z‖ ^ (2 * (K + 1)))
        * (2 * ‖z‖ / (‖z‖ + z.re)) ^ (K + 2) := by
  ring

theorem mem_digStirlingC {c : Ctx} (hc : c.Valid) {w : Nat} {Y : CBox} {K : Nat}
    {L : List ℚ} {z : ℂ} (hx : z ∈ Y)
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hz : 8 ≤ z.re) :
    Complex.digamma z ∈ digStirlingC c Y L K := by
  have hz0 : 0 < z.re := by
    have h := hz
    linarith
  obtain ⟨R, hR, hRb⟩ := Complex.dig_stirling_bound_sector z hz0 K
  rw [dig_tail_bridge K z] at hRb
  -- main + half terms
  have hlog : Complex.log z ∈ logBox c Y := mem_logBox c hc hx
  have hhalf : (1 : ℂ) / (2 * z)
      ∈ CBox.div (c.prec + 16) oneCBox
        (CBox.mul (c.prec + 16) (twoC (c.prec + 16)) Y) := by
    have h2 : (2 : ℂ) * z
        ∈ CBox.mul (c.prec + 16) (twoC (c.prec + 16)) Y :=
      CBox.mem_mul mem_twoC hx
    exact CBox.mem_div mem_oneCBox h2
  -- corrections: per-term membership (for `k < K`)
  have htermC : ∀ k : Nat, k ≤ K →
      -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1)))
        ∈ digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1) := by
    intro k hkK
    set Q : ℚ := -(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)) ) with hQ
    have hLk := hL (2 * (k + 1)) (by omega)
    have hQv : ((((Q : ℚ)) : ℝ) : ℂ)
        = -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ))) := by
      rw [hQ, hLk]
      norm_cast
    have hmemQ : ((((Q : ℚ)) : ℝ) : ℂ) / z ^ (2 * (k + 1))
        ∈ digCorrBoxC c Q Y (k + 1) :=
      CBox.mem_div (CBox.mem_ofReal (Ival.mem_ofRat _ _))
        (CBox.mem_npow hx _)
    have heq : ((((Q : ℚ)) : ℝ) : ℂ) / z ^ (2 * (k + 1))
        = -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ)
          / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))) := by
      rw [hQv, div_div]
    rwa [heq] at hmemQ
  have hfaC : List.Forall₂ (fun x B => x ∈ B)
      ((List.range K).map fun k =>
        -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))
      ((List.range K).map fun k =>
        digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)) :=
    csumForall₂RangeLe htermC K le_rfl
  have hS : (∑ k ∈ Finset.range K,
        -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))
      ∈ csumC (c.prec + 16)
        ((List.range K).map fun k =>
          digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)) := by
    have hmem := mem_csumC (c.prec + 16) _ _ hfaC
    rwa [csum_list_sum_map_range] at hmem
  have hMS : (Complex.log z - 1 / (2 * z))
      + (∑ k ∈ Finset.range K,
          -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))
      ∈ csumC (c.prec + 16)
        ([logBox c Y, CBox.neg (CBox.div (c.prec + 16) oneCBox
          (CBox.mul (c.prec + 16) (twoC (c.prec + 16)) Y))]
          ++ (List.range K).map fun k =>
            digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)) := by
    have hmem : ((Complex.log z :: -(1 / (2 * z)) :: (List.range K).map fun k =>
        -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))).sum
        ∈ csumC (c.prec + 16)
          (logBox c Y :: CBox.neg (CBox.div (c.prec + 16) oneCBox
            (CBox.mul (c.prec + 16) (twoC (c.prec + 16)) Y)) ::
            (List.range K).map fun k =>
              digCorrBoxC c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)) :=
      mem_csumC (c.prec + 16) _ _
        (List.Forall₂.cons hlog (List.Forall₂.cons
          (CBox.mem_neg hhalf) hfaC))
    have hlist : ((Complex.log z :: -(1 / (2 * z)) :: (List.range K).map fun k =>
        -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))).sum
        = (Complex.log z - 1 / (2 * z))
          + (∑ k ∈ Finset.range K,
              -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1)))) := by
      simp only [List.sum_cons]
      rw [csum_list_sum_map_range]
      ring
    rwa [hlist] at hmem
  -- tail (corrected bound: `2·scale` times the sector factor `^(K+2)`)
  have hT : (2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ))))) / ‖z‖ ^ (2 * (K + 1))
      * (2 * ‖z‖ / (‖z‖ + z.re)) ^ (K + 2)
      ∈ Ival.mul (c.prec + 16)
        (Ival.div (c.prec + 16)
          (Ival.ofRat (c.prec + 16)
            (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))))
          (Ival.npow (c.prec + 16) (CBox.norm (c.prec + 16) Y) (2 * (K + 1))))
        (secFactorC (c.prec + 16) Y (K + 2)) := by
    have hTreal : (2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ))))) / ‖z‖ ^ (2 * (K + 1))
        ∈ Ival.div (c.prec + 16)
          (Ival.ofRat (c.prec + 16)
            (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))))
          (Ival.npow (c.prec + 16) (CBox.norm (c.prec + 16) Y) (2 * (K + 1))) := by
      have hQT : (((2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ))) : ℚ)) : ℝ)
          = 2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ)))) := by
        have hLk := hL (2 * (K + 1)) (by omega)
        rw [hLk]
        push_cast
        ring
      have hmemQT : ((((2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ))) : ℚ))) : ℝ)
          ∈ Ival.ofRat (c.prec + 16)
            (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))) :=
        Ival.mem_ofRat _ _
      rw [hQT] at hmemQT
      exact Ival.mem_div hmemQT (Ival.mem_npow (CBox.mem_norm hx) _)
    exact Ival.mem_mul hTreal (mem_secFactorC hx)
  unfold digStirlingC
  simp only
  apply mem_widenCBox hMS
  intro m hm
  have hB : (2 * (|(((bernoulli (2 * (K + 1)) : ℚ)) : ℝ)| / ((2 * ((((K + 1) : ℕ)) : ℝ))))) / ‖z‖ ^ (2 * (K + 1))
      * (2 * ‖z‖ / (‖z‖ + z.re)) ^ (K + 2) ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  have hReq : Complex.digamma z
      - ((Complex.log z - 1 / (2 * z))
        + (∑ k ∈ Finset.range K,
            -(((bernoulli (2 * (k + 1)) : ℚ)) : ℂ) / ((2 * ((((k + 1) : ℕ)) : ℂ)) * z ^ (2 * (k + 1))))) = R := by
    linear_combination hR
  rw [hReq]
  exact le_trans hRb hB

/-! ### Shifted evaluation -/

/-- `ψ` on boxes with `Re > 0`: Stirling at `X + n` minus the shift sum. -/
def digammaPosC (c : Ctx) (X : CBox) (L : List ℚ) (n K : Nat) : CBox :=
  let w := c.prec + 16
  let Y := CBox.add w X (CBox.ofReal (Ival.ofRat w (n : ℚ)))
  let terms : List CBox := (List.range n).map fun k =>
    CBox.div w oneCBox (CBox.add w X (CBox.ofReal (Ival.ofRat w ((k : ℕ) : ℚ))))
  CBox.sub w (digStirlingC c Y L K) (csumC w terms)

theorem mem_digammaPosC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) (L : List ℚ) {n K : Nat}
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 8 ≤ (z + ((n : ℕ) : ℂ)).re)
    (hs : ∀ m : ℕ, z ≠ -(((m : ℕ)) : ℂ)) :
    Complex.digamma z ∈ digammaPosC c X L n K := by
  have hZn : z + ((n : ℕ) : ℂ)
      ∈ CBox.add (c.prec + 16) X (CBox.ofReal (Ival.ofRat (c.prec + 16) (n : ℚ))) :=
    CBox.mem_add hx (natCastC_mem_ofRat _ n)
  have hterm : ∀ k : Nat, (z + ((k : ℕ) : ℂ))⁻¹
      ∈ CBox.div (c.prec + 16) oneCBox
        (CBox.add (c.prec + 16) X (CBox.ofReal (Ival.ofRat (c.prec + 16) ((k : ℕ) : ℚ)))) := by
    intro k
    rw [← one_div]
    exact CBox.mem_div mem_oneCBox
      (CBox.mem_add hx (natCastC_mem_ofRat _ k))
  have hfaD : List.Forall₂ (fun x B => x ∈ B)
      ((List.range n).map fun k => (z + ((k : ℕ) : ℂ))⁻¹)
      ((List.range n).map fun k =>
        CBox.div (c.prec + 16) oneCBox
          (CBox.add (c.prec + 16) X (CBox.ofReal (Ival.ofRat (c.prec + 16) ((k : ℕ) : ℚ))))) :=
    csumForall₂Range hterm n
  have hdir : (Finset.range n).sum (fun k => (z + ((k : ℕ) : ℂ))⁻¹)
      ∈ csumC (c.prec + 16) ((List.range n).map fun k =>
        CBox.div (c.prec + 16) oneCBox
          (CBox.add (c.prec + 16) X (CBox.ofReal (Ival.ofRat (c.prec + 16) ((k : ℕ) : ℚ))))) := by
    have hmem := mem_csumC (c.prec + 16) _ _ hfaD
    rwa [csum_list_sum_map_range] at hmem
  have hStir : Complex.digamma (z + ((n : ℕ) : ℂ))
      ∈ digStirlingC c
        (CBox.add (c.prec + 16) X (CBox.ofReal (Ival.ofRat (c.prec + 16) (n : ℚ)))) L K :=
    mem_digStirlingC (w := c.prec + 16) hc hZn hL hK hY
  have hval : Complex.digamma z = Complex.digamma (z + ((n : ℕ) : ℂ))
      - ∑ k ∈ Finset.range n, (z + ((k : ℕ) : ℂ))⁻¹ :=
    digamma_shiftC hs n
  unfold digammaPosC
  simp only
  rw [hval]
  exact CBox.mem_sub hStir hdir

/-! ### Reflection -/

/-- `ψ` via `ψ(s) = ψ(1-s) - π·cot(πs)`. -/
def digammaReflC (c : Ctx) (X : CBox) (L : List ℚ) (n K : Nat) : CBox :=
  let w := c.prec + 16
  let oneSub := CBox.sub w (CBox.ofReal Ival.one) X
  let pos := digammaPosC c oneSub L n K
  let pix := CBox.mul w (CBox.ofReal c.pi) X
  let cot := CBox.div w (cosBox c pix) (sinBox c pix)
  CBox.sub w pos (CBox.mul w (CBox.ofReal c.pi) cot)

theorem mem_digammaReflC {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) (L : List ℚ) {n K : Nat}
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 8 ≤ ((1 : ℂ) - z + ((n : ℕ) : ℂ)).re)
    (hs : ∀ m : ℕ, (1 : ℂ) - z ≠ -(((m : ℕ)) : ℂ))
    (hsZ : ∀ n : ℤ, z ≠ ((n : ℤ) : ℂ)) :
    Complex.digamma z ∈ digammaReflC c X L n K := by
  have hpi : (Real.pi : ℂ) ∈ CBox.ofReal c.pi := CBox.mem_ofReal hc.pi_mem
  have h1c : (1 : ℂ) ∈ CBox.ofReal Ival.one := mem_oneC
  have hsub : (1 : ℂ) - z
      ∈ CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X :=
    CBox.mem_sub h1c hx
  have hpos : Complex.digamma ((1 : ℂ) - z)
      ∈ digammaPosC c (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) X) L n K :=
    mem_digammaPosC hc hsub _ hL hK hY hs
  have hmul : (Real.pi : ℂ) * z
      ∈ CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X :=
    CBox.mem_mul hpi hx
  have hcot : Complex.cot ((Real.pi : ℂ) * z)
      ∈ CBox.div (c.prec + 16)
        (cosBox c (CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X))
        (sinBox c (CBox.mul (c.prec + 16) (CBox.ofReal c.pi) X)) := by
    show Complex.cos ((Real.pi : ℂ) * z) / Complex.sin ((Real.pi : ℂ) * z) ∈ _
    exact CBox.mem_div (mem_cosBox c hc hmul) (mem_sinBox c hc hmul)
  have hrefl : Complex.digamma z = Complex.digamma (1 - z)
      - (Real.pi : ℂ) * Complex.cot ((Real.pi : ℂ) * z) := by
    have h := Complex.digamma_one_sub hsZ
    rw [h]
    ring
  unfold digammaReflC
  simp only
  rw [hrefl]
  exact CBox.mem_sub hpos (CBox.mem_mul hpi hcot)

/-! ### Top-level dispatch -/

/-- `ψ` on any box: poles → `⊤`; `Re > 0` → shift+Stirling; `Re < 0`
pole-free → reflection; else `⊤`. -/
def digammaCBox (c : Ctx) (X : CBox) : CBox :=
  match X.re.lo, X.re.hi, X.im.lo, X.im.hi with
  | some relo, some rehi, some ilo, some ihi =>
    if digHasPoleC relo rehi ilo ihi then CBox.top
    else
      let K := 4 + c.prec / 8
      let L := bernoulliList (2 * (K + 1))
      let X₀ := 20 + c.prec / 2
      if _hpos : 0 < relo.toRat then
        digammaPosC c X L (digShiftNumQ X₀ relo.toRat) K
      else if _hneg : rehi.toRat < 0 then
        digammaReflC c X L (digShiftNumQ X₀ (1 - rehi.toRat)) K
      else CBox.top
  | _, _, _, _ => CBox.top

theorem mem_digammaCBox {c : Ctx} (hc : c.Valid) {z : ℂ} {X : CBox}
    (hx : z ∈ X) : Complex.digamma z ∈ digammaCBox c X := by
  cases hlo : X.re.lo with
  | none =>
    cases hhi : X.re.hi with
    | none =>
      cases hloi : X.im.lo with
      | none =>
        cases hhii : X.im.hi with
        | none =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some _ =>
        have hev : digammaCBox c X = CBox.top := by
          simp [digammaCBox, hlo, hhi, hloi]
        rw [hev]; exact CBox.mem_top _
    | some _ =>
      have hev : digammaCBox c X = CBox.top := by
        simp [digammaCBox, hlo, hhi]
      rw [hev]; exact CBox.mem_top _
  | some relo =>
    cases hhi : X.re.hi with
    | none =>
      cases hloi : X.im.lo with
      | none =>
        cases hhii : X.im.hi with
        | none =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some _ =>
        have hev : digammaCBox c X = CBox.top := by
          simp [digammaCBox, hlo, hhi, hloi]
        rw [hev]; exact CBox.mem_top _
    | some rehi =>
      cases hloi : X.im.lo with
      | none =>
        cases hhii : X.im.hi with
        | none =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some _ =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
      | some ilo =>
        cases hhii : X.im.hi with
        | none =>
          have hev : digammaCBox c X = CBox.top := by
            simp [digammaCBox, hlo, hhi, hloi, hhii]
          rw [hev]; exact CBox.mem_top _
        | some ihi =>
          by_cases hpole : digHasPoleC relo rehi ilo ihi = true
          · have hev : digammaCBox c X = CBox.top := by
              simp [digammaCBox, hlo, hhi, hloi, hhii, hpole]
            rw [hev]; exact CBox.mem_top _
          · have hpoleF : digHasPoleC relo rehi ilo ihi = false := by
              simpa using hpole
            have hL : ∀ i : Nat, i ≤ 2 * ((4 + c.prec / 8) + 1) →
                ((bernoulliList (2 * ((4 + c.prec / 8) + 1))).getD i 0 : ℚ)
                  = bernoulli i := by
              intro i hi
              exact bernoulliList_getD _ _ hi
            have hpole' : ∀ m : ℕ, z ≠ -(((m : ℕ)) : ℂ) := by
              have hxr1 : ((relo.toRat : ℚ) : ℝ) ≤ z.re := mem_lo_le hx.1 hlo
              have hxr2 : z.re ≤ ((rehi.toRat : ℚ) : ℝ) := mem_le_hi hx.1 hhi
              have hxi1 : ((ilo.toRat : ℚ) : ℝ) ≤ z.im := mem_lo_le hx.2 hloi
              have hxi2 : z.im ≤ ((ihi.toRat : ℚ) : ℝ) := mem_le_hi hx.2 hhii
              intro m
              exact digHasPoleC_false hpoleF hxr1 hxr2 hxi1 hxi2 m
            by_cases hpos : 0 < relo.toRat
            · have hev : digammaCBox c X
                  = digammaPosC c X (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
                    (digShiftNumQ (20 + c.prec / 2) relo.toRat) (4 + c.prec / 8) := by
                simp [digammaCBox, hlo, hhi, hloi, hhii, hpoleF, eq_true hpos]
              rw [hev]
              have hY : 8 ≤ (z + (((digShiftNumQ (20 + c.prec / 2) relo.toRat) : ℕ) : ℂ)).re := by
                have hge := digShiftNumQ_ge (20 + c.prec / 2) relo.toRat
                have hre : ((relo.toRat : ℚ) : ℝ) ≤ z.re := mem_lo_le hx.1 hlo
                have ere : (z + (((digShiftNumQ (20 + c.prec / 2) relo.toRat) : ℕ) : ℂ)).re
                    = z.re + (((digShiftNumQ (20 + c.prec / 2) relo.toRat) : ℕ) : ℝ) := by
                  simp
                rw [ere]
                have hX : (8 : ℝ) ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
                  have hXb : 8 ≤ 20 + c.prec / 2 := by omega
                  exact_mod_cast hXb
                push_cast at hge ⊢
                linarith
              exact mem_digammaPosC hc hx _ hL (by omega) hY hpole'
            · by_cases hneg : rehi.toRat < 0
              · have hev : digammaCBox c X
                    = digammaReflC c X (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
                      (digShiftNumQ (20 + c.prec / 2) (1 - rehi.toRat)) (4 + c.prec / 8) := by
                  simp [digammaCBox, hlo, hhi, hloi, hhii, hpoleF, hpos, eq_true hneg]
                rw [hev]
                have hnegR : z.re < 0 := by
                  have h1 := mem_le_hi hx.1 hhi
                  have h2 : ((rehi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hneg
                  linarith
                have hY : 8 ≤ ((1 : ℂ) - z
                    + (((digShiftNumQ (20 + c.prec / 2) (1 - rehi.toRat) : Nat)) : ℂ)).re := by
                  have hge := digShiftNumQ_ge (20 + c.prec / 2) (1 - rehi.toRat)
                  have h5 : z.re ≤ ((rehi.toRat : ℚ) : ℝ) := mem_le_hi hx.1 hhi
                  have ere : ((1 : ℂ) - z
                      + (((digShiftNumQ (20 + c.prec / 2) (1 - rehi.toRat) : Nat)) : ℂ)).re
                      = 1 - z.re + (((digShiftNumQ (20 + c.prec / 2) (1 - rehi.toRat) : Nat)) : ℝ) := by
                    simp
                  rw [ere]
                  have hX : (8 : ℝ) ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
                    have hXb : 8 ≤ 20 + c.prec / 2 := by omega
                    exact_mod_cast hXb
                  have h4 : ((1 - rehi.toRat : ℚ) : ℝ) = 1 - ((rehi.toRat : ℚ) : ℝ) := by
                    push_cast; ring
                  push_cast at hge ⊢
                  linarith
                have hsZ : ∀ n : ℤ, z ≠ ((n : ℤ) : ℂ) := by
                  intro n h
                  have h' : z.re = ((n : ℤ) : ℝ) := by
                    have hr := congrArg Complex.re h
                    simpa using hr
                  rcases le_total 0 n with hn | hn
                  · have hnn : (0 : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast hn
                    linarith
                  · apply hpole' n.natAbs
                    have e : (n : ℤ) = -((((n.natAbs : ℕ)) : ℤ)) := by
                      rw [Int.ofNat_natAbs_of_nonpos hn]
                      exact (neg_neg n).symm
                    have e1 : ((n : ℤ) : ℂ) = -((((n.natAbs : ℕ))) : ℂ) := by
                      exact_mod_cast e
                    rw [h, e1]
                have hs1 : ∀ m : ℕ, (1 : ℂ) - z ≠ -(((m : ℕ)) : ℂ) := by
                  intro m hm
                  have hre : ((1 : ℂ) - z).re = 1 - z.re := by simp
                  have h1 : (1 : ℝ) - z.re ≥ 1 - 0 := by linarith
                  have hm0 : ((1 : ℂ) - z).re = -(((m : ℕ)) : ℝ) := by
                    have hr := congrArg Complex.re hm
                    simpa using hr
                  rw [hre] at hm0
                  have hnn : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg _
                  linarith
                exact mem_digammaReflC hc hx _ hL (by omega) hY hs1 hsZ
              · have hev : digammaCBox c X = CBox.top := by
                  simp [digammaCBox, hlo, hhi, hloi, hhii, hpoleF, hpos, hneg]
                rw [hev]; exact CBox.mem_top _

@[lynth_cfn] def digammaC : Fn1 .cplx .cplx where
  name := "Complex.digamma"
  graph x y := y = Complex.digamma x
  exu := exu_eq _
  ev := digammaCBox
  sound := fun _ _ _ _ hc hy hx => by obtain rfl := hy; exact mem_digammaCBox hc hx
  cost := 500

end Lynth.Interval.Fns
