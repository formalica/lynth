import Lynth.Interval.Fns.Gamma
import Lynth.Interval.Fns.Elem
import Lynth.Interval.Fns.Trig
import Lynth.Interval.Fns.Zeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Digamma function (real line, FLINT-style)

`ψ(x) = Γ'(x)/Γ(x)` following FLINT/Arb (`arb/digamma.c`, real case):
* positive `x`: shift up by `ψ(x+1) = ψ(x) + 1/x` until `y = x+n ≥ X₀`,
  then Stirling `ψ(y) ≈ ln y - 1/(2y) - Σ_{k=1}^{K} B_{2k}/(2k·y^{2k})`
  with explicit remainder (`2·T_{K+1}` widening).  One Bernoulli list
  `bernoulliList (2*(K+1))` per point (no per-term recomputation).
* negative non-pole `x`: reflection `ψ(x) = ψ(1-x) - π·cot(πx)`
  (`digamma_one_sub`); `1-x > 1` runs the positive path, `cot` via the
  verified `sin`/`cos` kernels.
* poles (nonpositive integers in the enclosure), `x = 0` straddles,
  unbounded → `⊤`.  No integer fast paths (`ψ(n) = H_{n-1} - γ` waived).

Analytic identities + remainder bounds are `sorry`'d here and mirrored in
`/tmp/digamma_thm.lean` (Mathlib-only, for the external prover, with the
Bernoulli block vendored so nothing is re-proved from scratch).
-/

namespace Lynth.Interval.Fns

open BigOperators

/-- real digamma as a real-valued function (graph for the registry entry). -/
noncomputable def rdig (s : ℝ) : ℝ := (Complex.digamma (s : ℂ)).re

/-- shift sum `Σ_{k<n} 1/(x+k)` (what the evaluator subtracts). -/
noncomputable def digShiftSum (x : ℝ) (n : Nat) : ℝ :=
  (Finset.range n).sum fun k => 1 / (x + (k : ℝ))

/-- one Stirling correction `-B_{2k}/(2k·y^{2k})` (may be positive or
negative; `B_{2k}` alternates).  For `k = 0` this is `0` (division by
zero); only `k ≥ 1` is ever used. -/
noncomputable def digCorrR (y : ℝ) (k : Nat) : ℝ :=
  -(bernoulli (2 * k) : ℝ) / ((2 * (k : ℝ)) * y ^ ((2 * (k : ℝ))))

/-- Stirling approximation `ln y - 1/(2y) + Σ_{k<K} C_{k+1}`. -/
noncomputable def digStirling (y : ℝ) (K : Nat) : ℝ :=
  Real.log y - 1 / (2 * y)
    + (Finset.range K).sum (fun k => digCorrR y (k + 1))

/-- first omitted correction scale `|B_{2K+2}|/((2K+2)·y^{2K+2})`. -/
noncomputable def digTailScale (y : ℝ) (K : Nat) : ℝ :=
  |(bernoulli (2 * (K + 1)) : ℝ)|
    / ((2 * (((K + 1 : Nat)) : ℝ)) * y ^ ((2 * (((K + 1 : Nat)) : ℝ))))

/-- EASY: the shift sum is what the evaluator subtracts (definitional). -/
theorem digShiftSum_eq (x : ℝ) (n : Nat) :
    digShiftSum x n = (Finset.range n).sum fun k => 1 / (x + (k : ℝ)) := by
  rfl

/-- SORRY (handoff `/tmp/digamma_thm.lean`): shift identity
`ψ(x) = ψ(x+n) - Σ_{k<n} 1/(x+k)` for `0 < x`. -/
theorem dig_shift (x : ℝ) (hx : 0 < x) (n : Nat) :
    rdig x = rdig (x + n) - digShiftSum x n := by
  sorry

/-- SORRY (handoff `/tmp/digamma_thm.lean`): Stirling identity with
remainder. For `0 < y`, `1 ≤ K`, `4*K+4 ≤ y`:
`|ψ(y) - (ln y - 1/(2y) + Σ corrections)| ≤ 2·T_{K+1}`. -/
theorem dig_stirling_bound (y : ℝ) (hy : 0 < y) (K : Nat)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ y) :
    |rdig y - digStirling y K| ≤ 2 * digTailScale y K := by
  sorry

/-- SORRY (handoff `/tmp/digamma_thm.lean`): reflection
`ψ(x) = ψ(1-x) - π·cos(πx)/sin(πx)` for `x < 0` non-integer. -/
theorem dig_refl (x : ℝ) (hx : x < 0) (hN : ∀ m : ℕ, x ≠ -(m : ℝ)) :
    rdig x = rdig (1 - x)
      - Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) := by
  sorry

/-- shift count clearing `X₀` above a rational lower bound
(`⌈X₀ - loQ⌉` for positive gaps, `0` otherwise). -/
def digShiftNumQ (X₀ : Nat) (loQ : ℚ) : Nat :=
  if (X₀ : ℚ) - loQ ≤ 0 then 0
  else (((X₀ : ℚ) - loQ).num.toNat / (((X₀ : ℚ) - loQ).den : Nat) + 1)

/-- the shift count always clears the target. -/
theorem digShiftNumQ_ge (X₀ : Nat) (loQ : ℚ) :
    (X₀ : ℝ) - (loQ : ℝ) ≤ ((digShiftNumQ X₀ loQ : Nat) : ℝ) := by
  unfold digShiftNumQ
  split
  · rename_i h
    have hR : (((X₀ : ℚ) - loQ : ℚ) : ℝ) ≤ 0 := by exact_mod_cast h
    push_cast at hR ⊢
    linarith
  · rename_i h
    have hpos : 0 < (X₀ : ℚ) - loQ := lt_of_not_ge h
    set d : ℚ := (X₀ : ℚ) - loQ with hd
    have hnum : 0 < d.num := by
      have hq : (0 : ℚ) < d := hpos
      rw [← d.num_div_den] at hq
      have hden : (0 : ℚ) < ((d.den : Nat) : ℚ) := by
        exact_mod_cast d.pos
      rw [div_pos_iff] at hq
      rcases hq with ⟨hh, _⟩ | ⟨_, hdd⟩
      · exact_mod_cast hh
      · have : ((d.den : Nat) : ℚ) < 0 := hdd
        linarith
    have hnn : 0 ≤ d.num := le_of_lt hnum
    have htn : ((d.num.toNat : Nat) : ℤ) = d.num := Int.toNat_of_nonneg hnn
    have hden1 : 1 ≤ d.den := by
      have hp := d.pos
      omega
    have hN : d.num.toNat ≤ (d.num.toNat / d.den + 1) * d.den := by
      have hdm := Nat.div_add_mod d.num.toNat d.den
      have hmod := Nat.mod_lt d.num.toNat (show 0 < d.den by omega)
      have hring : (d.num.toNat / d.den + 1) * d.den
          = d.den * (d.num.toNat / d.den) + d.den := by ring
      omega
    have hdenR : (0 : ℝ) < ((d.den : Nat) : ℝ) := by exact_mod_cast hden1
    have hle : ((d.num.toNat : Nat) : ℝ) / ((d.den : Nat) : ℝ)
        ≤ ((d.num.toNat / d.den + 1 : Nat) : ℝ) := by
      rw [div_le_iff₀ hdenR]
      have hc : ((d.num.toNat / d.den + 1 : Nat) : ℝ) * ((d.den : Nat) : ℝ)
          = (((d.num.toNat / d.den + 1) * d.den : Nat) : ℝ) := by
        push_cast
        ring
      rw [hc]
      exact_mod_cast hN
    have hqd : ((d.num.toNat : Nat) : ℝ) / ((d.den : Nat) : ℝ)
        = (X₀ : ℝ) - (loQ : ℝ) := by
      have htnR : ((d.num.toNat : Nat) : ℝ) = ((d.num : ℤ) : ℝ) := by
        exact_mod_cast htn
      have h1 : d = ((d.num : ℤ) : ℚ) / ((d.den : Nat) : ℚ) :=
        d.num_div_den.symm
      have h1R : ((d : ℚ) : ℝ)
          = ((d.num : ℤ) : ℝ) / ((d.den : Nat) : ℝ) := by
        exact_mod_cast h1
      rw [htnR, ← h1R, hd]
      push_cast
      ring
    show (X₀ : ℝ) - (loQ : ℝ) ≤ ((d.num.toNat / d.den + 1 : Nat) : ℝ)
    rw [← hqd]
    exact hle

/-- pole test: the enclosure contains a nonpositive integer. -/
def digHasPole (lo hi : Dy) : Bool :=
  decide (⌈lo.toRat⌉ ≤ ⌊hi.toRat⌋ ∧ ⌈lo.toRat⌉ ≤ 0)

/-- a negative pole test rules out every `x = -m`. -/
theorem digHasPole_false {lo hi : Dy} (h : digHasPole lo hi = false) (x : ℝ)
    (hlo : ((lo.toRat : ℚ) : ℝ) ≤ x) (hhi : x ≤ ((hi.toRat : ℚ) : ℝ))
    (m : Nat) : x ≠ -(m : ℝ) := by
  intro he
  subst he
  have e : ((-(m : ℤ) : ℚ) : ℝ) = (-(m : ℝ)) := by push_cast; ring
  have e1 : lo.toRat ≤ (-(m : ℤ) : ℚ) := by
    have h' : ((lo.toRat : ℚ) : ℝ) ≤ ((-(m : ℤ) : ℚ) : ℝ) := by
      rw [e]
      exact hlo
    exact_mod_cast h'
  have e2 : (-(m : ℤ) : ℚ) ≤ hi.toRat := by
    have h' : ((-(m : ℤ) : ℚ) : ℝ) ≤ ((hi.toRat : ℚ) : ℝ) := by
      rw [e]
      exact hhi
    exact_mod_cast h'
  have c1 : ⌈lo.toRat⌉ ≤ -(m : ℤ) := Int.ceil_le.mpr e1
  have c2 : -(m : ℤ) ≤ ⌊hi.toRat⌋ := Int.le_floor.mpr e2
  have h' := of_decide_eq_false h
  exact h' ⟨le_trans c1 c2, le_trans c1 (by omega)⟩

/-- one Stirling correction `Q/(Y^{2k})` with exact rational `Q`. -/
def digCorrTerm (c : Ctx) (Q : ℚ) (Y : Ival) (k : Nat) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec Q)
    (rpowIval c Y (Ival.ofRat c.prec ((2 * ((k : Nat) : ℚ)))))

/-- interval for the tail scale (mirrors the analytic scale). -/
def digTailIval (c : Ctx) (QT : ℚ) (Y : Ival) (K : Nat) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec QT)
    (rpowIval c Y (Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ))))))

/-- Stirling enclosure at `Y ∋ y` (log, half term, `K` corrections,
widened by the interval tail). -/
def digStirlingIval (c : Ctx) (Y : Ival) (L : List ℚ) (K : Nat) : Ival :=
  let logT := logIval c Y
  let halfT := Ival.div c.prec (Ival.ofRat c.prec 1)
    (Ival.mul c.prec (Ival.ofRat c.prec 2) Y)
  let corrs : List Ival := (List.range K).map fun k =>
    digCorrTerm c (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ)))) Y (k + 1)
  let sumPart := isum c ([logT, Ival.neg halfT] ++ corrs)
  let tail := digTailIval c
    (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ)))) Y K
  match tail.hi with
  | some h => Ival.add c.prec sumPart (Ival.ofRats c.prec (-h.toRat) h.toRat)
  | none => Ival.top

/-- positive enclosure at `X ∋ x`: Stirling at `Y = X + n` minus shift. -/
def digammaPosIval (c : Ctx) (X : Ival) (L : List ℚ) (n K : Nat) : Ival :=
  let Y := Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))
  let terms : List Ival := (List.range n).map fun k =>
    Ival.div c.prec (Ival.ofRat c.prec 1)
      (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))
  Ival.sub c.prec (digStirlingIval c Y L K) (isum c terms)

/-- reflection enclosure at `X ∋ x < 0`: positive path at `1-X` minus
`π·cos(πx)/sin(πx)`. -/
def digammaReflIval (c : Ctx) (X : Ival) (L : List ℚ) (n K : Nat) : Ival :=
  let oneSub := Ival.sub c.prec (Ival.ofRat c.prec 1) X
  let pos := digammaPosIval c oneSub L n K
  let pix := Ival.mul c.prec c.pi X
  let cot := Ival.div c.prec (cosIval c pix) (sinIval c pix)
  Ival.sub c.prec pos (Ival.mul c.prec c.pi cot)

/-- dispatcher: poles/straddles/unbounded → `⊤`; `0 < lo` → shift+Stirling
with adaptive `n`; `hi < 0` pole-free → reflection; else `⊤`. -/
def digammaIval (c : Ctx) (X : Ival) : Ival :=
  match X.lo, X.hi with
  | some lo, some hi =>
    if digHasPole lo hi then Ival.top
    else
      let K := 4 + c.prec / 8
      let L := bernoulliList (2 * (K + 1))
      if _hpos : 0 < lo.toRat then
        digammaPosIval c X L (digShiftNumQ (20 + c.prec / 2) lo.toRat) K
      else if _hneg : hi.toRat < 0 then
        digammaReflIval c X L (digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat)) K
      else Ival.top
  | _, _ => Ival.top

/-- list sum over a mapped range is the finset sum. -/
theorem dig_list_sum_map_range (f : Nat → ℝ) : ∀ N : Nat,
    ((List.range N).map f).sum = (Finset.range N).sum fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      Finset.sum_range_succ]
    rw [dig_list_sum_map_range f N]

theorem digammaPos_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (L : List ℚ) (hxMem : x ∈ X) (hx : 0 < x) (n K : Nat)
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ x + (n : ℝ)) :
    rdig x ∈ digammaPosIval c X L n K := by
  -- shifted enclosure membership
  have hnR : (((n : Nat) : ℚ) : ℝ) ∈ Ival.ofRat c.prec (n : ℚ) :=
    Ival.mem_ofRat _ _
  have hnR' : ((n : Nat) : ℝ) ∈ Ival.ofRat c.prec (n : ℚ) := by
    exact_mod_cast hnR
  have hYmem : x + (n : ℝ) ∈ Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)) :=
    Ival.mem_add hxMem hnR'
  -- shift-sum terms
  have hterm : ∀ k : Nat,
      1 / (x + ((k : Nat) : ℝ)) ∈ Ival.div c.prec (Ival.ofRat c.prec 1)
        (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ))) := by
    intro k
    have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
      exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
    have hk : (((k : Nat) : ℚ) : ℝ) ∈ Ival.ofRat c.prec ((k : Nat) : ℚ) :=
      Ival.mem_ofRat _ _
    have hkR : ((k : Nat) : ℝ) ∈ Ival.ofRat c.prec ((k : Nat) : ℚ) := by
      exact_mod_cast hk
    exact Ival.mem_div h1 (Ival.mem_add hxMem hkR)
  have hfaD : ∀ m : Nat, List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun k => 1 / (x + ((k : Nat) : ℝ)))
      ((List.range m).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))) := by
    intro m
    induction m with
    | zero => exact List.Forall₂.nil
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append ih
        (List.Forall₂.cons (hterm m) List.Forall₂.nil)
  have hdir : (Finset.range n).sum (fun k => 1 / (x + ((k : Nat) : ℝ)))
      ∈ isum c ((List.range n).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.add c.prec X (Ival.ofRat c.prec ((k : Nat) : ℚ)))) := by
    have hmem := mem_isum c hc _ _ (hfaD n)
    rwa [dig_list_sum_map_range] at hmem
  -- Stirling corrections: per-term membership (for `k ≤ K`)
  have hcorrM : ∀ k : Nat, k ≤ K → digCorrR (x + (n : ℝ)) (k + 1) ∈ digCorrTerm c
      (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ))))
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) (k + 1) := by
    intro k hkK
    set Q : ℚ := -(L.getD (2 * (k + 1)) 0) / (2 * ((k + 1 : Nat) : ℚ)) with hQ
    have hQmem : (Q : ℝ) ∈ Ival.ofRat c.prec Q := Ival.mem_ofRat _ _
    have hQeq : (Q : ℝ)
        = -(bernoulli (2 * (k + 1)) : ℝ) / (2 * (((k + 1 : Nat)) : ℝ)) := by
      rw [hQ]
      have hLk := hL (2 * (k + 1)) (by omega)
      rw [hLk]
      push_cast
      ring
    have h0exp : (2 : ℝ) * (((k + 1 : Nat)) : ℝ)
        ∈ Ival.ofRat c.prec ((2 * (((k + 1 : Nat) : ℚ)))) := by
      have h0 : (((2 * (((k + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          ∈ Ival.ofRat c.prec ((2 * (((k + 1 : Nat) : ℚ)))) :=
        Ival.mem_ofRat _ _
      have e : (((2 * (((k + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          = 2 * (((k + 1 : Nat)) : ℝ) := by push_cast; ring
      rwa [e] at h0
    unfold digCorrTerm
    simp only [digCorrR]
    have hval : -(bernoulli (2 * (k + 1)) : ℝ)
          / ((2 * (((k + 1 : Nat)) : ℝ)) * (x + (n : ℝ)) ^ ((2 * (((k + 1 : Nat)) : ℝ))))
        = (Q : ℝ) / (x + (n : ℝ)) ^ (2 * (((k + 1 : Nat)) : ℝ)) := by
      rw [hQeq, div_div]
    rw [hval]
    exact Ival.mem_div hQmem (mem_rpowIval hc hYmem h0exp)
  have hfaC : ∀ m : Nat, m ≤ K → List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun k => digCorrR (x + (n : ℝ)) (k + 1))
      ((List.range m).map fun k => digCorrTerm c
        (-(L.getD (2 * (k + 1)) 0) / (2 * (((k + 1 : Nat) : ℚ))))
        (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) (k + 1)) := by
    intro m
    induction m with
    | zero => intro _; exact List.Forall₂.nil
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append (ih (by omega))
        (List.Forall₂.cons (hcorrM m (by omega)) List.Forall₂.nil)
  -- log + half terms
  have hlogM : Real.log (x + (n : ℝ)) ∈ logIval c
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) :=
    mem_logIval hc hYmem
  have hhalfM : 1 / (2 * (x + (n : ℝ))) ∈ Ival.div c.prec
      (Ival.ofRat c.prec 1)
      (Ival.mul c.prec (Ival.ofRat c.prec 2)
        (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)))) := by
    have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
      exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
    have h2R : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by
      exact_mod_cast Ival.mem_ofRat c.prec (2 : ℚ)
    exact Ival.mem_div h1 (Ival.mem_mul h2R hYmem)
  -- tail scale membership
  have htailM : 2 * digTailScale (x + (n : ℝ)) K ∈ digTailIval c
      (2 * |(L.getD (2 * (K + 1)) 0)| / (2 * (((K + 1 : Nat) : ℚ))))
      (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))) K := by
    set QT : ℚ := 2 * |(L.getD (2 * (K + 1)) 0)| / (2 * ((K + 1 : Nat) : ℚ)) with hQT
    have hBmem : (QT : ℝ) ∈ Ival.ofRat c.prec QT := Ival.mem_ofRat _ _
    have hQeqT : (QT : ℝ)
        = 2 * |(bernoulli (2 * (K + 1)) : ℝ)| / (2 * (((K + 1 : Nat)) : ℝ)) := by
      rw [hQT]
      have hLK := hL (2 * (K + 1)) (by omega)
      rw [hLK]
      push_cast
      ring_nf
    have h0T : (2 : ℝ) * (((K + 1 : Nat)) : ℝ)
        ∈ Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ)))) := by
      have h0 : (((2 * (((K + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          ∈ Ival.ofRat c.prec ((2 * (((K + 1 : Nat) : ℚ)))) :=
        Ival.mem_ofRat _ _
      have e : (((2 * (((K + 1 : Nat) : ℚ)) : ℚ)) : ℝ)
          = 2 * (((K + 1 : Nat)) : ℝ) := by push_cast; ring
      rwa [e] at h0
    have hvalT : 2 * digTailScale (x + (n : ℝ)) K
        = (QT : ℝ) / (x + (n : ℝ)) ^ (2 * (((K + 1 : Nat)) : ℝ)) := by
      simp only [digTailScale]
      rw [hQeqT, div_div]
      ring
    rw [hvalT]
    exact Ival.mem_div hBmem (mem_rpowIval hc hYmem h0T)
  -- analytic master bound + sum assembly + widen finish
  have hpos : (0 : ℝ) < x + (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ ((n : Nat) : ℝ) := by exact_mod_cast Nat.zero_le n
    linarith
  have hmaster := dig_stirling_bound (x + (n : ℝ)) hpos K hK hY
  have hfaLH : List.Forall₂ (fun x I => x ∈ I)
      [Real.log (x + (n : ℝ)), -(1 / (2 * (x + (n : ℝ))))]
      [logIval c (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ))),
        Ival.neg (Ival.div c.prec (Ival.ofRat c.prec 1)
          (Ival.mul c.prec (Ival.ofRat c.prec 2)
            (Ival.add c.prec X (Ival.ofRat c.prec (n : ℚ)))))] := by
    refine List.Forall₂.cons hlogM (List.Forall₂.cons ?_ List.Forall₂.nil)
    exact Ival.mem_neg hhalfM
  have hfaAll := List.rel_append hfaLH (hfaC K le_rfl)
  have hsumM := mem_isum c hc _ _ hfaAll
  have hsumEq : (([Real.log (x + (n : ℝ)), -(1 / (2 * (x + (n : ℝ))))]
        ++ ((List.range K).map (fun k => digCorrR (x + (n : ℝ)) (k + 1))))).sum
      = (Real.log (x + (n : ℝ)) - 1 / (2 * (x + (n : ℝ)))
        + (Finset.range K).sum (fun k => digCorrR (x + (n : ℝ)) (k + 1))) := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [dig_list_sum_map_range]
    ring
  rw [hsumEq] at hsumM
  simp only [digammaPosIval, digStirlingIval]
  split
  · rename_i h hiH
    have h2Tle : 2 * digTailScale (x + (n : ℝ)) K ≤ h.toReal := by
      have h2 := htailM
      rw [Ival.mem_def, hiH] at h2
      simp only [Ival.leHi_some] at h2
      exact h2.2
    rw [Dy.toReal_def] at h2Tle
    have habs := abs_le.mp hmaster
    simp only [digStirling] at habs
    have heq : rdig x
        = ((digStirling (x + (n : ℝ)) K
          + (rdig (x + (n : ℝ)) - digStirling (x + (n : ℝ)) K))
          - (Finset.range n).sum (fun k => 1 / (x + ((k : Nat) : ℝ)))) := by
      have hsh := dig_shift x hx n
      rw [digShiftSum_eq] at hsh
      rw [hsh]
      ring
    have hRmem : rdig (x + (n : ℝ))
        - (Real.log (x + (n : ℝ)) - 1 / (2 * (x + (n : ℝ)))
          + (Finset.range K).sum (fun k => digCorrR (x + (n : ℝ)) (k + 1)))
        ∈ Ival.ofRats c.prec (-h.toRat) h.toRat := by
      refine Ival.mem_ofRats ?_ ?_ <;>
        (push_cast at habs h2Tle ⊢; linarith [habs.1, habs.2, h2Tle])
    rw [heq]
    simp only [digStirling]
    exact Ival.mem_sub (Ival.mem_add hsumM hRmem) hdir
  · exact Ival.mem_top _

theorem digammaRefl_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (L : List ℚ) (hxMem : x ∈ X) (hx : x < 0)
    (hN : ∀ m : ℕ, x ≠ -(m : ℝ)) (n K : Nat)
    (hL : ∀ i : Nat, i ≤ 2 * (K + 1) → (L.getD i 0 : ℚ) = bernoulli i)
    (hK : 1 ≤ K) (hY : 4 * (K : ℝ) + 4 ≤ (1 - x) + (n : ℝ)) :
    rdig x ∈ digammaReflIval c X L n K := by
  have h1R : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
    exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
  have h1x : 1 - x ∈ Ival.sub c.prec (Ival.ofRat c.prec 1) X :=
    Ival.mem_sub h1R hxMem
  have hx' : 0 < 1 - x := by linarith
  have hpos := digammaPos_sound c hc (1 - x)
    (Ival.sub c.prec (Ival.ofRat c.prec 1) X) L h1x hx' n K hL hK hY
  have hpi : Real.pi ∈ c.pi := hc.pi_mem
  have hpix : Real.pi * x ∈ Ival.mul c.prec c.pi X :=
    Ival.mem_mul hpi hxMem
  have hcos : Real.cos (Real.pi * x) ∈ cosIval c (Ival.mul c.prec c.pi X) :=
    mem_cosIval hc hpix
  have hsin : Real.sin (Real.pi * x) ∈ sinIval c (Ival.mul c.prec c.pi X) :=
    mem_sinIval hc hpix
  have hcot : Real.cos (Real.pi * x) / Real.sin (Real.pi * x) ∈ Ival.div c.prec
      (cosIval c (Ival.mul c.prec c.pi X)) (sinIval c (Ival.mul c.prec c.pi X)) :=
    Ival.mem_div hcos hsin
  have hpicot : Real.pi * (Real.cos (Real.pi * x) / Real.sin (Real.pi * x)) ∈
      Ival.mul c.prec c.pi (Ival.div c.prec
        (cosIval c (Ival.mul c.prec c.pi X))
        (sinIval c (Ival.mul c.prec c.pi X))) :=
    Ival.mem_mul hpi hcot
  have hre := dig_refl x hx hN
  simp only [digammaReflIval]
  rw [hre]
  exact Ival.mem_sub hpos hpicot

theorem digammaIval_sound (c : Ctx) (hc : c.Valid) (x : ℝ) (X : Ival)
    (hx : x ∈ X) : rdig x ∈ digammaIval c X := by
  obtain ⟨hxlo, hxhi⟩ := hx
  cases hlo : X.lo with
  | none =>
    cases hhi : X.hi with
    | none => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
  | some lo =>
    cases hhi : X.hi with
    | none => simp only [digammaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi =>
      have hloR : lo.toReal ≤ x := hxlo lo hlo
      have hhiR : x ≤ hi.toReal := hxhi hi hhi
      rw [Dy.toReal_def] at hloR hhiR
      have hxM : x ∈ X := Ival.mem_def.mpr ⟨hxlo, hxhi⟩
      simp only [digammaIval, hlo, hhi]
      split
      · rename_i hpole
        exact Ival.mem_top _
      · rename_i hpole
        have hpoleF : digHasPole lo hi = false := Bool.eq_false_iff.mpr hpole
        have hN : ∀ m : Nat, x ≠ -(m : ℝ) := fun m =>
          digHasPole_false hpoleF x hloR hhiR m
        split
        · rename_i hpos
          show rdig x ∈ digammaPosIval c X
            (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
            (digShiftNumQ (20 + c.prec / 2) lo.toRat) (4 + c.prec / 8)
          have hx0 : 0 < x := by
            have hlor : (0 : ℝ) < (lo.toRat : ℝ) := by
              exact_mod_cast hpos
            linarith
          have hL : ∀ i : Nat, i ≤ 2 * ((4 + c.prec / 8) + 1) →
              ((bernoulliList (2 * ((4 + c.prec / 8) + 1))).getD i 0 : ℚ)
                = bernoulli i := fun i hi => bernoulliList_getD _ _ hi
          have hK : 1 ≤ 4 + c.prec / 8 := by omega
          have hXK : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
              ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
            have hnat : 4 * (4 + c.prec / 8) + 4 ≤ 20 + c.prec / 2 := by omega
            exact_mod_cast hnat
          have hY : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
              ≤ x + ((digShiftNumQ (20 + c.prec / 2) lo.toRat : Nat) : ℝ) := by
            have hn := digShiftNumQ_ge (20 + c.prec / 2) lo.toRat
            push_cast at hn hXK ⊢
            linarith [hloR, hn, hXK]
          exact digammaPos_sound c hc x X _ hxM hx0 _ _ hL hK hY
        · rename_i hnpos
          split
          · rename_i hneg
            show rdig x ∈ digammaReflIval c X
              (bernoulliList (2 * ((4 + c.prec / 8) + 1)))
              (digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat)) (4 + c.prec / 8)
            have hxneg : x < 0 := by
              have hhir : (hi.toRat : ℝ) < 0 := by exact_mod_cast hneg
              linarith
            have hL : ∀ i : Nat, i ≤ 2 * ((4 + c.prec / 8) + 1) →
                ((bernoulliList (2 * ((4 + c.prec / 8) + 1))).getD i 0 : ℚ)
                  = bernoulli i := fun i hi => bernoulliList_getD _ _ hi
            have hK : 1 ≤ 4 + c.prec / 8 := by omega
            have hXK : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
                ≤ ((20 + c.prec / 2 : Nat) : ℝ) := by
              have hnat : 4 * (4 + c.prec / 8) + 4 ≤ 20 + c.prec / 2 := by omega
              exact_mod_cast hnat
            have hY : 4 * ((4 + c.prec / 8 : Nat) : ℝ) + 4
                ≤ (1 - x)
                  + ((digShiftNumQ (20 + c.prec / 2) (1 - hi.toRat) : Nat) : ℝ) := by
              have hn := digShiftNumQ_ge (20 + c.prec / 2) (1 - hi.toRat)
              have hcast : ((1 - hi.toRat : ℚ) : ℝ)
                  = 1 - (hi.toRat : ℝ) := by push_cast; ring
              push_cast at hn hXK hcast ⊢
              linarith [hhiR, hn, hcast, hXK]
            exact digammaRefl_sound c hc x X _ hxM hxneg hN _ _ hL hK hY
          · rename_i hneg2
            exact Ival.mem_top _

@[lynth_fn] def digammaR : Fn1 .real .real where
  name := "digamma"
  graph x y := y = rdig x
  exu := exu_eq _
  ev c X := digammaIval c X
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    exact digammaIval_sound c hc x X hx
  cost := 800

end Lynth.Interval.Fns
