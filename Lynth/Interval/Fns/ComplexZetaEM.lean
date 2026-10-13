import Lynth.Interval.Fns.ComplexGamma
import Lynth.Interval.Fns.ComplexElem
import Lynth.Interval.Fns.Zeta

/-!
# Complex Euler–Maclaurin zeta (`0 < Re ≠ 1`).

Mirror of the real Euler–Maclaurin evaluator (`zetaEMIval`,
`Lynth/Interval/Fns/Zeta.lean`): direct `cpow` sum, the `(N+1)^{1-s}/(s-1)`
integral term, the `(N+1)^{-s}/2` half term, Bernoulli corrections with
complex rising factorials, all widened by an explicit interval tail.
The one analytic input — the complex EM expansion with remainder — is
stated below as a mirror of `/tmp/complex/zeta_em_handoff.lean` (same
contract as the other mirrors: keep byte-identical, paste the prover's
proof back).  Everything else is proved inline.
-/

namespace Complex

/-- one complex Bernoulli correction (evaluator form, matches the handoff). -/
noncomputable def emCorrCh (s : ℂ) (N r : Nat) : ℂ :=
  (((bernoulli (2 * r) : ℚ)) : ℂ) / ((((Nat.factorial (2 * r) : ℕ))) : ℂ)
    * ((Finset.range (2 * r - 1)).prod fun j => s + ((((j : ℕ))) : ℂ))
    / ((((N + 1 : ℕ))) : ℂ) ^ (s + (2 * ((((r : ℕ))) : ℂ)) - 1)

/-- complex tail scale (real-valued, matches the handoff). -/
noncomputable def emTailCh (s : ℂ) (N M : Nat) : ℝ :=
  |(((bernoulli (2 * (M + 1)) : ℚ)) : ℝ)| / ((((Nat.factorial (2 * (M + 1)) : ℕ))) : ℝ)
    * ‖(Finset.range (2 * (M + 1) - 1)).prod fun j => s + ((((j : ℕ))) : ℂ)‖
    / (((N + 1 : ℕ)) : ℝ) ^ (s.re + (2 * (((M + 1 : Nat)) : ℝ)) - 1)

/-- COMPLEX EULER–MACLAURIN (zeta with explicit remainder).
Mirror of `/tmp/complex/zeta_em_handoff.lean` for the external prover. -/
theorem zeta_em_bound (s : ℂ) (hs : 0 < s.re) (hs1 : s.re ≠ 1) (N M : Nat)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : s.re + 2 * M + 2 ≤ (((N + 1 : ℕ)) : ℝ)) :
    ∃ R : ℂ, riemannZeta s
        = (∑ k ∈ Finset.range N, ((((k + 1 : ℕ))) : ℂ) ^ (-s))
          + ((((N + 1 : ℕ))) : ℂ) ^ (1 - s) / (s - 1)
          + ((((N + 1 : ℕ))) : ℂ) ^ (-s) / 2
          + (∑ r ∈ Finset.range M, emCorrCh s N (r + 1)) + R
      ∧ ‖R‖ ≤ 2 * emTailCh s N M := by
  sorry

end Complex

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Rising bridge -/

/-- recursive rising factorial is the finset product. -/
theorem risingCx_eq_prod (x : ℂ) (r : Nat) :
    risingCx x r = (Finset.range r).prod fun j => x + ((j : ℕ) : ℂ) := by
  induction r with
  | zero => simp [risingCx]
  | succ r ih =>
    simp only [risingCx, Finset.prod_range_succ, ih]

/-! ### Correction boxes -/

/-- one correction box `Q·R/(Np1^{s+2r-1})`. -/
def emCorrBoxC (c : Ctx) (S Np1 : CBox) (Q : ℚ) (r : Nat) : CBox :=
  let w := c.prec + 16
  CBox.div w
    (CBox.mul w (CBox.ofReal (Ival.ofRat w Q)) (risingC w S (2 * r - 1)))
    (expBox c (CBox.mul c.prec (logBox c Np1)
      (CBox.add w S (CBox.ofReal (Ival.ofRat w ((2 * ((r : Nat) : ℚ)) - 1))))))

/-- Euler–Maclaurin enclosure at `S ∋ s` (`0 < Re s ≠ 1` from the guard). -/
def zetaEMC (c : Ctx) (S : CBox) (N M : Nat) : CBox :=
  let w := c.prec + 16
  let Np1 := CBox.ofReal (Ival.ofRat w ((N + 1 : Nat) : ℚ))
  let terms : List CBox := (List.range N).map fun k =>
    expBox c (CBox.mul c.prec
      (logBox c (CBox.ofReal (Ival.ofRat w (((k + 1 : Nat)) : ℚ))))
      (CBox.neg S))
  let intTerm := CBox.div w
    (expBox c (CBox.mul c.prec (logBox c Np1)
      (CBox.sub w (CBox.ofReal Ival.one) S)))
    (CBox.sub w S (CBox.ofReal Ival.one))
  let halfTerm := CBox.div w
    (expBox c (CBox.mul c.prec (logBox c Np1) (CBox.neg S)))
    (twoC w)
  let corrs : List CBox := (List.range M).map fun r =>
    emCorrBoxC c S Np1
      (bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ)) (r + 1)
  let sumPart := CBox.add w (csumC w terms)
    (CBox.add w intTerm (CBox.add w halfTerm (csumC w corrs)))
  let tail := Ival.div w
    (Ival.mul w
      (Ival.ofRat w (2 * |(bernoulliQ (2 * (M + 1)))|
        / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ)))
      (CBox.norm w (risingC w S (2 * (M + 1) - 1))))
    (rpowIval c (Ival.ofRat w (((N + 1 : Nat)) : ℚ))
      (Ival.add w S.re (Ival.ofRat w ((2 * (((M + 1 : Nat)) : ℚ)) - 1))))
  widenCBox w sumPart (Ival.magHi tail)

theorem mem_zetaEMC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox} {N M : Nat}
    (hx : z ∈ S) (hs : 0 < z.re) (hs1 : z.re ≠ 1)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : z.re + 2 * M + 2 ≤ ((((N + 1 : Nat))) : ℝ)) :
    riemannZeta z ∈ zetaEMC c S N M := by
  obtain ⟨R, hR, hRb⟩ := Complex.zeta_em_bound z hs hs1 N M hN hM hNM
  -- direct terms
  have hterm : ∀ k : Nat, ((((k + 1 : ℕ))) : ℂ) ^ (-z)
      ∈ expBox c (CBox.mul c.prec
        (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((k + 1 : Nat)) : ℚ))))
        (CBox.neg S)) := by
    intro k
    have hb0 : ((((k + 1 : ℕ))) : ℂ) ≠ 0 := by
      have h1 : (0 : ℕ) < k + 1 := Nat.zero_lt_succ k
      exact_mod_cast (ne_of_gt h1)
    exact mem_cpow_point hc (natCastC_mem_ofRat _ (k + 1)) hb0 (CBox.mem_neg hx)
  have hdirT : (Finset.range N).sum (fun k => ((((k + 1 : ℕ))) : ℂ) ^ (-z))
      ∈ csumC (c.prec + 16) ((List.range N).map fun k =>
        expBox c (CBox.mul c.prec
          (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((k + 1 : Nat)) : ℚ))))
          (CBox.neg S))) := by
    have hmem := mem_csumC (c.prec + 16) _ _
      (csumForall₂Range hterm N)
    rwa [csum_list_sum_map_range] at hmem
  -- N+1 point facts
  have hNp1mem : ((((N + 1 : ℕ))) : ℂ)
      ∈ CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)) :=
    natCastC_mem_ofRat _ (N + 1)
  have hNp10 : ((((N + 1 : ℕ))) : ℂ) ≠ 0 := by
    have h1 : (0 : ℕ) < N + 1 := Nat.zero_lt_succ N
    exact_mod_cast (ne_of_gt h1)
  -- integral term
  have hint : ((((N + 1 : ℕ))) : ℂ) ^ (1 - z) / (z - 1)
      ∈ CBox.div (c.prec + 16)
        (expBox c (CBox.mul c.prec
          (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))))
          (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) S)))
        (CBox.sub (c.prec + 16) S (CBox.ofReal Ival.one)) :=
    CBox.mem_div
      (mem_cpow_point hc hNp1mem hNp10 (CBox.mem_sub mem_oneC hx))
      (CBox.mem_sub hx mem_oneC)
  -- half term
  have hhalfT : ((((N + 1 : ℕ))) : ℂ) ^ (-z) / 2
      ∈ CBox.div (c.prec + 16)
        (expBox c (CBox.mul c.prec
          (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))))
          (CBox.neg S)))
        (twoC (c.prec + 16)) :=
    CBox.mem_div
      (mem_cpow_point hc hNp1mem hNp10 (CBox.mem_neg hx))
      mem_twoC
  -- corrections
  have hcorrT : ∀ r : Nat, r ≤ M → Complex.emCorrCh z N (r + 1)
      ∈ emCorrBoxC c S
        (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)))
        (bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ)) (r + 1) := by
    intro r hrM
    set Q : ℚ := bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ) with hQ
    have hbq : bernoulliQ (2 * (r + 1)) = bernoulli (2 * (r + 1)) := by
      rw [bernoulliQ]
      exact bernoulliList_getD _ _ le_rfl
    have hQv : (((Q : ℝ)) : ℂ)
        = (((bernoulli (2 * (r + 1)) : ℚ)) : ℂ) / ((((Nat.factorial (2 * (r + 1)) : ℕ))) : ℂ) := by
      simp only [hQ, hbq, Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, Rat.cast_one,
          Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_natCast,
          Complex.ofReal_one, Complex.ofReal_ratCast, Rat.cast_div, Complex.ofReal_div, Rat.cast_ofNat, Nat.cast_ofNat]
    have hQmem : (((Q : ℝ)) : ℂ)
        ∈ CBox.ofReal (Ival.ofRat (c.prec + 16) Q) :=
      CBox.mem_ofReal (Ival.mem_ofRat _ _)
    have hRising : risingCx z (2 * (r + 1) - 1)
        ∈ risingC (c.prec + 16) S (2 * (r + 1) - 1) :=
      mem_risingC hx _
    set E : ℚ := (2 * (((r + 1 : Nat)) : ℚ) - 1) with hE
    have hExp : z + (((E : ℝ)) : ℂ)
        ∈ CBox.add (c.prec + 16) S
          (CBox.ofReal (Ival.ofRat (c.prec + 16) E)) :=
      CBox.mem_add hx (CBox.mem_ofReal (Ival.mem_ofRat _ _))
    have hden : ((((N + 1 : ℕ))) : ℂ) ^ (z + (((E : ℝ)) : ℂ))
        ∈ expBox c (CBox.mul c.prec
          (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))))
          (CBox.add (c.prec + 16) S
            (CBox.ofReal (Ival.ofRat (c.prec + 16) ((2 * (((r + 1 : Nat)) : ℚ)) - 1))))) :=
      mem_cpow_point hc hNp1mem hNp10 hExp
    have hmemQ : (((Q : ℝ)) : ℂ) * risingCx z (2 * (r + 1) - 1)
        / ((((N + 1 : ℕ))) : ℂ) ^ (z + (((E : ℝ)) : ℂ))
        ∈ emCorrBoxC c S
          (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))) Q (r + 1) := by
      unfold emCorrBoxC
      simp only
      exact CBox.mem_div (CBox.mem_mul hQmem hRising) hden
    have heq : (((Q : ℝ)) : ℂ) * risingCx z (2 * (r + 1) - 1)
        / ((((N + 1 : ℕ))) : ℂ) ^ (z + (((E : ℝ)) : ℂ))
        = Complex.emCorrCh z N (r + 1) := by
      unfold Complex.emCorrCh
      rw [hQv, risingCx_eq_prod]
      have hexp : z + (((E : ℝ)) : ℂ)
          = z + (2 * ((((r + 1 : ℕ))) : ℂ)) - 1 := by
        rw [hE]
        push_cast
        ring
      rw [hexp]
    rwa [heq] at hmemQ
  -- correction sum
  have hfaC : List.Forall₂ (fun x B => x ∈ B)
      ((List.range M).map fun r => Complex.emCorrCh z N (r + 1))
      ((List.range M).map fun r =>
        emCorrBoxC c S
          (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)))
          (bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ)) (r + 1)) :=
    csumForall₂RangeLe hcorrT M le_rfl
  have hS : (∑ r ∈ Finset.range M, Complex.emCorrCh z N (r + 1))
      ∈ csumC (c.prec + 16) ((List.range M).map fun r =>
        emCorrBoxC c S
          (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)))
          (bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ)) (r + 1)) := by
    have hmem := mem_csumC (c.prec + 16) _ _ hfaC
    rwa [csum_list_sum_map_range] at hmem
  -- nested assembly (avoids Forall₂-append lemmas)
  have hMS : ((∑ k ∈ Finset.range N, ((((k + 1 : ℕ))) : ℂ) ^ (-z))
      + (((((N + 1 : ℕ))) : ℂ) ^ (1 - z) / (z - 1)
        + (((((N + 1 : ℕ))) : ℂ) ^ (-z) / 2
          + (∑ r ∈ Finset.range M, Complex.emCorrCh z N (r + 1)))))
      ∈ CBox.add (c.prec + 16) (csumC (c.prec + 16) ((List.range N).map fun k =>
        expBox c (CBox.mul c.prec
          (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((k + 1 : Nat)) : ℚ))))
          (CBox.neg S))))
        (CBox.add (c.prec + 16)
          (CBox.div (c.prec + 16)
            (expBox c (CBox.mul c.prec
              (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))))
              (CBox.sub (c.prec + 16) (CBox.ofReal Ival.one) S)))
            (CBox.sub (c.prec + 16) S (CBox.ofReal Ival.one)))
          (CBox.add (c.prec + 16)
            (CBox.div (c.prec + 16)
              (expBox c (CBox.mul c.prec
                (logBox c (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))))
                (CBox.neg S)))
              (twoC (c.prec + 16)))
            (csumC (c.prec + 16) ((List.range M).map fun r =>
              emCorrBoxC c S
                (CBox.ofReal (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)))
                (bernoulliQ (2 * (r + 1)) / ((Nat.factorial (2 * (r + 1)) : Nat) : ℚ)) (r + 1))))) := by
    have hval : ((∑ k ∈ Finset.range N, ((((k + 1 : ℕ))) : ℂ) ^ (-z))
        + (((((N + 1 : ℕ))) : ℂ) ^ (1 - z) / (z - 1)
          + (((((N + 1 : ℕ))) : ℂ) ^ (-z) / 2
            + (∑ r ∈ Finset.range M, Complex.emCorrCh z N (r + 1)))))
        = ((∑ k ∈ Finset.range N, ((((k + 1 : ℕ))) : ℂ) ^ (-z)))
          + ((((((N + 1 : ℕ))) : ℂ) ^ (1 - z) / (z - 1)
            + (((((N + 1 : ℕ))) : ℂ) ^ (-z) / 2
              + (∑ r ∈ Finset.range M, Complex.emCorrCh z N (r + 1))))) := by
      ring
    rw [hval]
    exact CBox.mem_add hdirT
      (CBox.mem_add hint (CBox.mem_add hhalfT hS))
  -- tail
  have hT : 2 * Complex.emTailCh z N M
        ∈ Ival.div (c.prec + 16)
          (Ival.mul (c.prec + 16)
            (Ival.ofRat (c.prec + 16)
              (2 * |(bernoulliQ (2 * (M + 1)))| / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ)))
            (CBox.norm (c.prec + 16) (risingC (c.prec + 16) S (2 * (M + 1) - 1))))
          (rpowIval c (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))
            (Ival.add (c.prec + 16) S.re
              (Ival.ofRat (c.prec + 16) ((2 * ((((M + 1 : Nat))) : ℚ)) - 1)))) := by
    have hbq : bernoulliQ (2 * (M + 1)) = bernoulli (2 * (M + 1)) := by
      rw [bernoulliQ]
      exact bernoulliList_getD _ _ le_rfl
    have hmemQT : ((2 * |(bernoulliQ (2 * (M + 1)))|
          / (Nat.factorial (2 * (M + 1)) : ℚ) : ℚ) : ℝ)
        ∈ Ival.ofRat (c.prec + 16)
          (2 * |(bernoulliQ (2 * (M + 1)))| / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ)) :=
      Ival.mem_ofRat _ _
    have hRisingN : ‖risingCx z (2 * (M + 1) - 1)‖
        ∈ CBox.norm (c.prec + 16) (risingC (c.prec + 16) S (2 * (M + 1) - 1)) :=
      CBox.mem_norm (mem_risingC hx _)
    have hQeqE : (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = 2 * (((M + 1 : Nat)) : ℝ) - 1 := by
      push_cast
      ring
    have h0exp : z.re + (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        ∈ Ival.add (c.prec + 16) S.re
          (Ival.ofRat (c.prec + 16) ((2 * (((M + 1 : Nat)) : ℚ)) - 1)) :=
      Ival.mem_add hx.1 (Ival.mem_ofRat _ _)
    have eexp : z.re + (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = z.re + 2 * (((M + 1 : Nat)) : ℝ) - 1 := by
      rw [hQeqE]; abel
    have hsig : z.re + 2 * (((M + 1 : Nat)) : ℝ) - 1
        ∈ Ival.add (c.prec + 16) S.re
          (Ival.ofRat (c.prec + 16) ((2 * (((M + 1 : Nat)) : ℚ)) - 1)) := by
      rwa [eexp] at h0exp
    have hrpow : ((((N + 1 : ℕ))) : ℝ) ^ (z.re + 2 * (((M + 1 : Nat)) : ℝ) - 1)
        ∈ rpowIval c (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))
          (Ival.add (c.prec + 16) S.re
            (Ival.ofRat (c.prec + 16) ((2 * (((M + 1 : Nat)) : ℚ)) - 1))) := by
      have hP : ((((N + 1 : ℕ))) : ℝ) ∈ Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ) := by
        have h := Ival.mem_ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ)
        rwa [Rat.cast_natCast] at h
      exact mem_rpowIval hc hP hsig
    have hdiv : ((2 * |(bernoulliQ (2 * (M + 1)))|
        / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ) : ℚ) : ℝ)
        * ‖risingCx z (2 * (M + 1) - 1)‖ / (((N + 1 : ℕ)) : ℝ) ^ (z.re + (2 * ((((M + 1 : ℕ))) : ℝ)) - 1)
        ∈ Ival.div (c.prec + 16)
          (Ival.mul (c.prec + 16)
            (Ival.ofRat (c.prec + 16)
              (2 * |(bernoulliQ (2 * (M + 1)))| / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ)))
            (CBox.norm (c.prec + 16) (risingC (c.prec + 16) S (2 * (M + 1) - 1))))
          (rpowIval c (Ival.ofRat (c.prec + 16) (((N + 1 : Nat)) : ℚ))
            (Ival.add (c.prec + 16) S.re
              (Ival.ofRat (c.prec + 16) ((2 * ((((M + 1 : Nat))) : ℚ)) - 1)))) :=
      Ival.mem_div (Ival.mem_mul hmemQT hRisingN) hrpow
    have hTeq : ((2 * |(bernoulliQ (2 * (M + 1)))|
        / ((Nat.factorial (2 * (M + 1)) : Nat) : ℚ) : ℚ) : ℝ)
        * ‖risingCx z (2 * (M + 1) - 1)‖ / (((N + 1 : ℕ)) : ℝ) ^ (z.re + (2 * ((((M + 1 : ℕ))) : ℝ)) - 1)
        = 2 * Complex.emTailCh z N M := by
      unfold Complex.emTailCh
      push_cast
      rw [bernoulliQ_cast, risingCx_eq_prod]
      ring
    rwa [hTeq] at hdiv
  unfold zetaEMC
  simp only
  apply mem_widenCBox hMS
  intro m hm
  have hB : 2 * Complex.emTailCh z N M ≤ m.toReal :=
    le_trans (le_abs_self _) (Ival.abs_le_magHi hT hm)
  have hReq : riemannZeta z
      - (((∑ k ∈ Finset.range N, ((((k + 1 : ℕ))) : ℂ) ^ (-z))
        + (((((N + 1 : ℕ))) : ℂ) ^ (1 - z) / (z - 1)
          + (((((N + 1 : ℕ))) : ℂ) ^ (-z) / 2
            + (∑ r ∈ Finset.range M, Complex.emCorrCh z N (r + 1)))))) = R := by
    linear_combination hR
  rw [hReq]
  exact le_trans hRb hB

/-! ### Guarded dispatch (`0 < Re ≠ 1`) -/

/-- EM guard: `0 < Re ≠ 1` enclosures → Euler–Maclaurin with adaptive `N`;
everything else → `⊤` (mirror of `zetaEMGuard`). -/
def zetaEMGuardC (c : Ctx) (S : CBox) (relo rehi : Dy) : CBox :=
  if _hpos : 0 < relo.toRat ∧ (rehi.toRat < 1 ∨ 1 < relo.toRat) then
    let M := 4 + c.prec / 8
    let sHi := rehi.toRat.num.toNat
    let N := (16 + c.prec / 2) ⊔ (sHi + 2 * M + 2)
    zetaEMC c S N M
  else CBox.top

theorem mem_zetaEMGuardC {c : Ctx} (hc : c.Valid) {z : ℂ} {S : CBox}
    (hx : z ∈ S) {relo rehi : Dy}
    (hlo : S.re.lo = some relo) (hhi : S.re.hi = some rehi) :
    riemannZeta z ∈ zetaEMGuardC c S relo rehi := by
  have hloR : ((relo.toRat : ℚ) : ℝ) ≤ z.re := mem_lo_le hx.1 hlo
  have hhiR : z.re ≤ ((rehi.toRat : ℚ) : ℝ) := mem_le_hi hx.1 hhi
  simp only [zetaEMGuardC]
  split
  · rename_i hpos
    show riemannZeta z ∈ zetaEMC c S
      ((16 + c.prec / 2) ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2))
      (4 + c.prec / 8)
    have hlor : (0 : ℝ) < (relo.toRat : ℝ) := by exact_mod_cast hpos.1
    have hs : 0 < z.re := lt_of_lt_of_le hlor hloR
    have hs1 : z.re ≠ 1 := by
      rcases hpos.2 with hlt | hgt
      · have h1 : ((rehi.toRat : ℚ) : ℝ) < 1 := by exact_mod_cast hlt
        have hlt' : z.re < 1 := lt_of_le_of_lt hhiR h1
        exact ne_of_lt hlt'
      · have h1 : (1 : ℝ) < ((relo.toRat : ℚ) : ℝ) := by exact_mod_cast hgt
        have hgt' : (1 : ℝ) < z.re := lt_of_lt_of_le h1 hloR
        exact ne_of_gt hgt'
    have hM : 1 ≤ 4 + c.prec / 8 := by omega
    have hN : 1 ≤ (16 + c.prec / 2)
        ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) := by
      have h16 : 1 ≤ 16 + c.prec / 2 := by omega
      exact le_trans h16 le_sup_left
    have hle_q : relo.toRat ≤ rehi.toRat := by
      by_contra hlt
      have hlt' : rehi.toRat < relo.toRat := not_le.mp hlt
      have hltR : ((rehi.toRat : ℚ) : ℝ) < ((relo.toRat : ℚ) : ℝ) := by
        exact_mod_cast hlt'
      linarith
    have hhi_pos : 0 < rehi.toRat := lt_of_lt_of_le hpos.1 hle_q
    have hnn : 0 ≤ rehi.toRat.num := by
      have hq : (0 : ℚ) < rehi.toRat := hhi_pos
      rw [← rehi.toRat.num_div_den] at hq
      have hden : (0 : ℚ) < (rehi.toRat.den : ℚ) := by
        have hd := rehi.toRat.pos
        exact_mod_cast hd
      rw [div_pos_iff] at hq
      rcases hq with ⟨h, _⟩ | ⟨_, hd⟩
      · have hlt : (0 : ℤ) < rehi.toRat.num := by exact_mod_cast h
        exact le_of_lt hlt
      · have hlt : (rehi.toRat.den : ℚ) < 0 := hd
        linarith
    have htn : ((rehi.toRat.num.toNat : Nat) : ℤ) = rehi.toRat.num :=
      Int.toNat_of_nonneg hnn
    have hqi : ((rehi.toRat : ℚ) : ℝ) ≤ (rehi.toRat.num.toNat : ℝ) := by
      have hdiv : ((rehi.toRat : ℚ) : ℝ)
          = (rehi.toRat.num : ℝ) / (rehi.toRat.den : ℝ) := by
        conv_lhs => rw [← rehi.toRat.num_div_den]
        push_cast
        ring
      rw [hdiv]
      have heq : (rehi.toRat.num.toNat : ℝ) = (rehi.toRat.num : ℝ) := by
        exact_mod_cast htn
      rw [heq]
      have hnum_nn : (0 : ℝ) ≤ (rehi.toRat.num : ℝ) := by
        exact_mod_cast hnn
      have hden_ge : (1 : ℝ) ≤ (rehi.toRat.den : ℝ) := by
        have hd1 : 1 ≤ rehi.toRat.den := by
          have h := rehi.toRat.pos
          omega
        exact_mod_cast hd1
      exact div_le_self hnum_nn hden_ge
    have hsHi : z.re ≤ (rehi.toRat.num.toNat : ℝ) :=
      le_trans hhiR hqi
    have hNM : z.re + 2 * ((4 + c.prec / 8 : Nat) : ℝ) + 2
        ≤ ((((16 + c.prec / 2)
          ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 : Nat)) : ℝ) := by
      have hB : ((rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2 : Nat) : ℝ)
          ≤ ((((16 + c.prec / 2)
            ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) : Nat)) : ℝ) := by
        exact_mod_cast le_sup_right
      have hcast : ((rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2 : Nat) : ℝ)
          = (rehi.toRat.num.toNat : ℝ)
            + 2 * ((4 + c.prec / 8 : Nat) : ℝ) + 2 := by
        push_cast
        ring
      have hNp1 : ((((16 + c.prec / 2)
          ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) : Nat)) : ℝ)
          ≤ ((((16 + c.prec / 2)
            ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 : Nat)) : ℝ) := by
        have hle : (16 + c.prec / 2)
            ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2)
            ≤ (16 + c.prec / 2)
              ⊔ (rehi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 := by
          omega
        exact_mod_cast hle
      linarith [hsHi]
    exact mem_zetaEMC hc hx hs hs1 hN hM hNM
  · exact CBox.mem_top _

end Lynth.Interval.Fns
