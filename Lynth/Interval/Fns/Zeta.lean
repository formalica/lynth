import Lynth.Interval.Fns.Gamma
import Lynth.Interval.Fns.ZetaEulerProd
import Lynth.Interval.Fns.ZetaEM
import Lynth.Interval.Fns.Trig
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Riemann zeta via FLINT's split (real line only)

* Integer points `n ≥ 6` → Euler product (`arb/zeta_ui.c`,
  `acb_dirichlet/euler_product_real_ui.c`): `ζ(n) = ∏_p (1 - p⁻ⁿ)⁻¹`
  with tail `Π·P^{1-n}/(n-1)`.  FLINT uses the product for large `n`
  (where Bernoulli loses); small integers `2–5` go through Euler–Maclaurin
  below — no Bernoulli/Borwein/Apéry fast paths (waived).
* `0 < s ≠ 1` (non-integers and small integers uniformly) →
  Euler–Maclaurin (`acb_poly/zeta_em_sum.c`): direct sum plus
  `(N+1)^{1-s}/(s-1)`, half term, and `M` Bernoulli corrections.
* `s < 0` (strictly negative enclosures) → functional equation
  (`acb_zeta` for `Re s < 0`):
  `ζ(s) = 2^s·π^{s-1}·sin(πs/2)·Γ(1-s)·ζ(1-s)` with `1-s > 1`
  through the non-recursive positive dispatch.
* `s = 0` straddles, `s = 1` (or enclosures touching it) → `⊤`
  (the pole is indeterminate).  No complex/Hurwitz/Riemann–Siegel.

Bernoulli numbers reuse `bernoulliQ`/`bernoulliList_getD` (`Fns/Gamma.lean`).
Analytic identities + remainder bounds live in the ported modules
`Fns/ZetaEulerProd.lean`, `Fns/ZetaEM.lean` (proved by the external prover
from Mathlib-only `/tmp/zeta_*_thm.lean` handoffs); the FE identity is
proved in-file (ported from the external prover via `/tmp/zeta_neg_thm.lean`).
-/

namespace Lynth.Interval.Fns

open BigOperators

/-- real zeta as a real-valued function (graph for the registry entry). -/
noncomputable def zetaReal (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

/-- fold `Ival.add` over interval summands. -/
def isum (c : Ctx) : List Ival → Ival
  | [] => Ival.ofRat c.prec 0
  | I :: Is => Ival.add c.prec I (isum c Is)

theorem mem_isum (c : Ctx) (hc : c.Valid) (xs : List ℝ) (Is : List Ival)
    (h : List.Forall₂ (fun x I => x ∈ I) xs Is) :
    xs.sum ∈ isum c Is := by
  induction h with
  | nil => simpa [isum] using Ival.mem_ofRat c.prec 0
  | cons hx _ ih =>
    simp only [isum, List.sum_cons]
    exact Ival.mem_add hx (ih)

/-- fold `Ival.mul` over interval factors. -/
def iprod (c : Ctx) : List Ival → Ival
  | [] => Ival.ofRat c.prec 1
  | I :: Is => Ival.mul c.prec I (iprod c Is)

theorem mem_iprod (c : Ctx) (hc : c.Valid) (xs : List ℝ) (Is : List Ival)
    (h : List.Forall₂ (fun x I => x ∈ I) xs Is) :
    xs.prod ∈ iprod c Is := by
  induction h with
  | nil => simpa [iprod] using Ival.mem_ofRat c.prec 1
  | cons hx _ ih =>
    simp only [iprod, List.prod_cons]
    exact Ival.mem_mul hx (ih)

/-- one Euler factor `1/(1 - p⁻ⁿ)` at integer `n`, as an interval. -/
def eulerFactor (c : Ctx) (n p : Nat) : Ival :=
  Ival.div c.prec (Ival.ofRat c.prec 1)
    (Ival.sub c.prec (Ival.ofRat c.prec 1)
      (Ival.ofRat c.prec ((1 : ℚ) / (p ^ n : Nat))))

theorem mem_eulerFactor (c : Ctx) (hc : c.Valid) (n p : Nat) :
    (1 : ℝ) / (1 - 1 / (p ^ n : ℝ)) ∈ eulerFactor c n p := by
  unfold eulerFactor
  refine Ival.mem_div (by simpa using Ival.mem_ofRat c.prec (1 : ℚ)) ?_
  refine Ival.mem_sub (by simpa using Ival.mem_ofRat c.prec (1 : ℚ)) ?_
  have h : ((1 : ℚ) / (p ^ n : Nat) : ℝ) = 1 / (p ^ n : ℝ) := by
    push_cast; ring
  simpa [h] using Ival.mem_ofRat c.prec ((1 : ℚ) / (p ^ n : Nat))

/-- Euler-product enclosure at integer `n ≥ 2` (cutoff `P`). -/
def zetaEulerProdIval (c : Ctx) (n P : Nat) : Ival :=
  let ps := eulerPrimes P
  let prod := iprod c (ps.map fun p => eulerFactor c n p)
  let E : ℚ := 2 / (((P ^ (n - 1) : Nat) : ℚ) * ((n : ℚ) - 1))
  match prod.lo, prod.hi with
  | some lo, some hi =>
    Ival.ofRats c.prec (lo.toRat - E) (hi.toRat + E)
  | _, _ => Ival.top

theorem zetaEulerProd_sound (c : Ctx) (hc : c.Valid) (n P : Nat) (hn : 2 ≤ n)
    (hP : 2 ≤ P) :
    zetaReal n ∈ zetaEulerProdIval c n P := by
  have hmap : List.Forall₂ (fun x I => x ∈ I)
      ((eulerPrimes P).map fun p => (1 : ℝ) / (1 - 1 / (p ^ n : ℝ)))
      ((eulerPrimes P).map fun p => eulerFactor c n p) := by
    induction (eulerPrimes P) with
    | nil => exact List.Forall₂.nil
    | cons p ps ih => exact List.Forall₂.cons (mem_eulerFactor c hc n p) ih
  have hprod : eulerProd n P
      ∈ iprod c ((eulerPrimes P).map fun p => eulerFactor c n p) := by
    have h := mem_iprod c hc _ _ hmap
    simpa [eulerProd] using h
  have htail := zeta_eulerprod_tail n P hn hP
  have hE : ((2 / (((P ^ (n - 1) : Nat) : ℚ) * ((n : ℚ) - 1)) : ℚ) : ℝ)
      = 2 / (((P ^ (n - 1) : Nat) : ℝ) * ((n : ℝ) - 1)) := by
    push_cast; ring
  simp only [zetaEulerProdIval]
  split
  · rename_i lo hi hlo hhi
    have hmem := hprod
    rw [Ival.mem_def, hlo, hhi] at hmem
    simp only [Ival.loLe_some, Ival.leHi_some] at hmem
    obtain ⟨hlo', hhi'⟩ := hmem
    have hlo2 : lo.toReal ≤ eulerProd n P := hlo'
    have hhi2 : eulerProd n P ≤ hi.toReal := hhi'
    have habs := abs_le.mp htail
    unfold zetaReal
    rw [Dy.toReal_def] at hlo2 hhi2
    push_cast at hlo2 hhi2 habs hE ⊢
    refine Ival.mem_ofRats ?_ ?_ <;>
      simp only [Rat.cast_sub, Rat.cast_add] <;> push_cast <;>
        linarith [hlo2, hhi2, habs.1, habs.2, hE]
  · exact Ival.mem_top _

/-- local rising product with soundness stated directly in `emRising` form
(avoids translating Gamma's `risingReal`). -/
def risingZ (c : Ctx) (S : Ival) : Nat → Ival
  | 0 => Ival.ofRat c.prec 1
  | k + 1 => Ival.mul c.prec (risingZ c S k)
    (Ival.add c.prec S (Ival.ofRat c.prec (k : ℚ)))

theorem mem_risingZ (c : Ctx) (hc : c.Valid) (S : Ival) (s : ℝ) (hS : s ∈ S) :
    ∀ k : Nat, emRising s k ∈ risingZ c S k
  | 0 => by simpa [emRising, risingZ] using Ival.mem_ofRat c.prec 1
  | k + 1 => by
    have hk : ((k : ℚ) : ℝ) ∈ Ival.ofRat c.prec (k : ℚ) := Ival.mem_ofRat _ _
    have hsk : s + (k : ℝ) ∈ Ival.add c.prec S (Ival.ofRat c.prec (k : ℚ)) := by
      have e : ((k : ℚ) : ℝ) = (k : ℝ) := by exact_mod_cast rfl
      rw [e] at hk
      exact Ival.mem_add hS hk
    have h : emRising s k * (s + (k : ℝ)) ∈ Ival.mul c.prec (risingZ c S k)
        (Ival.add c.prec S (Ival.ofRat c.prec (k : ℚ))) :=
      Ival.mem_mul (mem_risingZ c hc S s hS k) hsk
    simpa [emRising, risingZ, Finset.prod_range_succ] using h

/-- one Bernoulli correction
`B_{2r}/(2r)! · rising(s,2r-1)/(N+1)^{s+2r-1}` (all interval ops). -/
def emCorrTerm (c : Ctx) (S Np1 : Ival) (r : Nat) : Ival :=
  let B : ℚ := bernoulliQ (2 * r) / (Nat.factorial (2 * r) : ℚ)
  Ival.div c.prec
    (Ival.mul c.prec (Ival.ofRat c.prec B) (risingZ c S (2 * r - 1)))
    (rpowIval c Np1 (Ival.add c.prec S (Ival.ofRat c.prec ((2 * (r : ℚ)) - 1))))

/-- interval for `2·emTailScale` (mirrors the analytic scale). -/
def emTailIval (c : Ctx) (S Np1 : Ival) (M : Nat) : Ival :=
  let B : ℚ := 2 * |(bernoulliQ (2 * (M + 1)))| / (Nat.factorial (2 * (M + 1)) : ℚ)
  Ival.div c.prec
    (Ival.mul c.prec (Ival.ofRat c.prec B) (risingZ c S (2 * (M + 1) - 1)))
    (rpowIval c Np1 (Ival.add c.prec S (Ival.ofRat c.prec ((2 * (((M + 1 : Nat) : ℚ))) - 1))))

/-- Euler–Maclaurin enclosure at `S ∋ s` (`0 < s ≠ 1` from the guard). -/
def zetaEMIval (c : Ctx) (S : Ival) (N M : Nat) : Ival :=
  let terms : List Ival := (List.range N).map fun k =>
    Ival.div c.prec (Ival.ofRat c.prec 1)
      (rpowIval c (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)) S)
  let Np1 := Ival.ofRat c.prec ((N + 1 : Nat) : ℚ)
  let intTerm := Ival.div c.prec
    (rpowIval c Np1 (Ival.sub c.prec (Ival.ofRat c.prec 1) S))
    (Ival.sub c.prec S (Ival.ofRat c.prec 1))
  let halfTerm := Ival.div c.prec
    (rpowIval c Np1 (Ival.sub c.prec (Ival.ofRat c.prec 0) S))
    (Ival.ofRat c.prec 2)
  let corrs : List Ival := (List.range M).map fun r => emCorrTerm c S Np1 (r + 1)
  let sumPart := isum c (terms ++ [intTerm, halfTerm] ++ corrs)
  let tail := emTailIval c S Np1 M
  match tail.hi with
  | some h => Ival.add c.prec sumPart (Ival.ofRats c.prec (-h.toRat) h.toRat)
  | none => Ival.top

/-- list sum over a mapped range is the finset sum. -/
theorem list_sum_map_range (f : Nat → ℝ) : ∀ N : Nat,
    ((List.range N).map f).sum = (Finset.range N).sum fun k => f k
  | 0 => by simp
  | N + 1 => by
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.sum_append, List.sum_cons, List.sum_nil, add_zero,
      Finset.sum_range_succ]
    rw [list_sum_map_range f N]

/-- Bernoulli values agree (`bernoulliQ` is Mathlib `bernoulli`). -/
theorem bernoulliQ_cast (r : Nat) :
    ((bernoulliQ (2 * r) : ℚ) : ℝ) = (bernoulli (2 * r) : ℝ) := by
  rw [bernoulliQ]
  have h : 2 * r ≤ 2 * r := Nat.le_refl _
  rw [bernoulliList_getD _ _ h]

theorem zetaEM_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (S : Ival)
    (hsMem : s ∈ S) (hs : 0 < s) (hs1 : s ≠ 1) (N M : Nat)
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : s + 2 * M + 2 ≤ (N + 1 : Nat)) :
    zetaReal s ∈ zetaEMIval c S N M := by
  -- per-term real values in analytic form
  have hterm : ∀ k : Nat,
      ((k + 1 : Nat) : ℝ) ^ (-s) ∈ Ival.div c.prec (Ival.ofRat c.prec 1)
        (rpowIval c (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)) S) := by
    intro k
    have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 :=
      by exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
    have hbase : (((k + 1 : Nat) : ℚ) : ℝ)
        ∈ Ival.ofRat c.prec ((k + 1 : Nat) : ℚ) := Ival.mem_ofRat _ _
    have hrp := mem_rpowIval hc hbase hsMem
    have hpos : (0 : ℝ) ≤ ((k + 1 : Nat) : ℝ) := by positivity
    have e : ((k + 1 : Nat) : ℝ) ^ (-s) = 1 / ((k + 1 : Nat) : ℝ) ^ s := by
      rw [Real.rpow_neg hpos]; ring
    rw [e]
    exact Ival.mem_div h1 hrp
  -- direct sum by induction on `N`
  have hfaD : ∀ n : Nat, List.Forall₂ (fun x I => x ∈ I)
      ((List.range n).map fun k => ((k + 1 : Nat) : ℝ) ^ (-s))
      ((List.range n).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (rpowIval c (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)) S)) := by
    intro n
    induction n with
    | zero => exact List.Forall₂.nil
    | succ n ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append ih
        (List.Forall₂.cons (hterm n) List.Forall₂.nil)
  have hdir : (Finset.range N).sum (fun k => ((k + 1 : Nat) : ℝ) ^ (-s))
      ∈ isum c ((List.range N).map fun k =>
        Ival.div c.prec (Ival.ofRat c.prec 1)
          (rpowIval c (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)) S)) := by
    have hmem := mem_isum c hc _ _ (hfaD N)
    rwa [list_sum_map_range] at hmem
  have hcorrM : ∀ r : Nat, emCorr s N (r + 1) ∈ emCorrTerm c S
      (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ)) (r + 1) := by
    intro r
    have hR := mem_risingZ c hc S s hsMem (2 * (r + 1) - 1)
    have hNp1 : (((N + 1 : Nat) : ℚ) : ℝ)
        ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) := Ival.mem_ofRat _ _
    have hNp1R : ((N + 1 : Nat) : ℝ) ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) := by
      exact_mod_cast hNp1
    have hQeq : (((2 * (((r + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = 2 * (((r + 1 : Nat)) : ℝ) - 1 := by push_cast; ring
    have h0exp : s + (((2 * (((r + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        ∈ Ival.add c.prec S
          (Ival.ofRat c.prec ((2 * (((r + 1 : Nat) : ℚ))) - 1)) :=
      Ival.mem_add hsMem (Ival.mem_ofRat _ _)
    have eexp : s + (((2 * (((r + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = s + 2 * (((r + 1 : Nat)) : ℝ) - 1 := by
      rw [hQeq]; abel
    have hexp : s + 2 * (((r + 1 : Nat)) : ℝ) - 1
        ∈ Ival.add c.prec S
          (Ival.ofRat c.prec ((2 * (((r + 1 : Nat) : ℚ))) - 1)) := by
      rwa [eexp] at h0exp
    unfold emCorrTerm
    simp only [emCorr]
    refine Ival.mem_div (Ival.mem_mul ?_ hR) (mem_rpowIval hc hNp1R hexp)
    · simpa [bernoulliQ_cast] using Ival.mem_ofRat c.prec
        (bernoulliQ (2 * (r + 1)) / (Nat.factorial (2 * (r + 1)) : ℚ))
  have hfaC : ∀ m : Nat, List.Forall₂ (fun x I => x ∈ I)
      ((List.range m).map fun r => emCorr s N (r + 1))
      ((List.range m).map fun r => emCorrTerm c S
        (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ)) (r + 1)) := by
    intro m
    induction m with
    | zero => exact List.Forall₂.nil
    | succ m ih =>
      rw [List.range_succ, List.map_append, List.map_append]
      exact List.rel_append ih
        (List.Forall₂.cons (hcorrM m) List.Forall₂.nil)
  -- integral + half terms (analytic form)
  have hNp1 : (((N + 1 : Nat) : ℚ) : ℝ) ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) :=
    Ival.mem_ofRat _ _
  have hNp1R : ((N + 1 : Nat) : ℝ) ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) := by
    exact_mod_cast hNp1
  have hintM : ((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1) ∈ Ival.div c.prec
      (rpowIval c (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ))
        (Ival.sub c.prec (Ival.ofRat c.prec 1) S))
      (Ival.sub c.prec S (Ival.ofRat c.prec 1)) := by
    have e1 : ((1 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 1 := Ival.mem_ofRat _ _
    have e1R : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by exact_mod_cast e1
    exact Ival.mem_div
      (mem_rpowIval hc hNp1R (Ival.mem_sub e1R hsMem))
      (Ival.mem_sub hsMem e1R)
  have hhalfM : ((N + 1 : Nat) : ℝ) ^ (-s) / 2 ∈ Ival.div c.prec
      (rpowIval c (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ))
        (Ival.sub c.prec (Ival.ofRat c.prec 0) S))
      (Ival.ofRat c.prec 2) := by
    have e0 : ((0 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 0 := Ival.mem_ofRat _ _
    have e0R : (0 : ℝ) ∈ Ival.ofRat c.prec 0 := by exact_mod_cast e0
    have e2 : ((2 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 2 := Ival.mem_ofRat _ _
    have e2R : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by exact_mod_cast e2
    have hexp0 : (0 : ℝ) - s ∈ Ival.sub c.prec (Ival.ofRat c.prec 0) S :=
      Ival.mem_sub e0R hsMem
    rw [zero_sub] at hexp0
    exact Ival.mem_div (mem_rpowIval hc hNp1R hexp0) e2R
  -- Bernoulli corrections: per-term membership (analytic form)
  -- tail scale membership (same shape at `M+1` with factor 2)
  have htailM : 2 * emTailScale s N M ∈ emTailIval c S
      (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ)) M := by
    have hR := mem_risingZ c hc S s hsMem (2 * (M + 1) - 1)
    have hNp1 : (((N + 1 : Nat) : ℚ) : ℝ)
        ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) := Ival.mem_ofRat _ _
    have hNp1R : ((N + 1 : Nat) : ℝ) ∈ Ival.ofRat c.prec ((N + 1 : Nat) : ℚ) := by
      exact_mod_cast hNp1
    have hQeq : (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = 2 * (((M + 1 : Nat)) : ℝ) - 1 := by push_cast; ring
    have h0exp : s + (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        ∈ Ival.add c.prec S
          (Ival.ofRat c.prec ((2 * (((M + 1 : Nat) : ℚ))) - 1)) :=
      Ival.mem_add hsMem (Ival.mem_ofRat _ _)
    have eexp : s + (((2 * (((M + 1 : Nat) : ℚ)) - 1 : ℚ)) : ℝ)
        = s + 2 * (((M + 1 : Nat)) : ℝ) - 1 := by
      rw [hQeq]; abel
    have hexpM : s + 2 * (((M + 1 : Nat)) : ℝ) - 1
        ∈ Ival.add c.prec S
          (Ival.ofRat c.prec ((2 * (((M + 1 : Nat) : ℚ))) - 1)) := by
      rwa [eexp] at h0exp
    have hBmem : ((2 * |(bernoulliQ (2 * (M + 1)))|
          / (Nat.factorial (2 * (M + 1)) : ℚ) : ℚ) : ℝ)
        ∈ Ival.ofRat c.prec
          (2 * |(bernoulliQ (2 * (M + 1)))| / (Nat.factorial (2 * (M + 1)) : ℚ)) :=
      Ival.mem_ofRat _ _
    have hval : 2 * emTailScale s N M
        = ((2 * |(bernoulliQ (2 * (M + 1)))|
            / (Nat.factorial (2 * (M + 1)) : ℚ) : ℚ) : ℝ)
          * emRising s (2 * (M + 1) - 1)
          / ((N + 1 : Nat) : ℝ) ^ (s + 2 * (((M + 1 : Nat)) : ℝ) - 1) := by
      unfold emTailScale
      push_cast
      rw [bernoulliQ_cast]
      ring
    rw [hval]
    exact Ival.mem_div
      (Ival.mem_mul hBmem hR) (mem_rpowIval hc hNp1R hexpM)
  -- assembled sum membership
  have hfaIH : List.Forall₂ (fun x I => x ∈ I)
      [((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1),
        ((N + 1 : Nat) : ℝ) ^ (-s) / 2]
      [Ival.div c.prec
        (rpowIval c (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ))
          (Ival.sub c.prec (Ival.ofRat c.prec 1) S))
        (Ival.sub c.prec S (Ival.ofRat c.prec 1)),
        Ival.div c.prec
        (rpowIval c (Ival.ofRat c.prec ((N + 1 : Nat) : ℚ))
          (Ival.sub c.prec (Ival.ofRat c.prec 0) S))
        (Ival.ofRat c.prec 2)] := by
    refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
    · -- integral term value
      have e1 : ((1 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 1 := Ival.mem_ofRat _ _
      have e1R : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by exact_mod_cast e1
      exact Ival.mem_div
        (mem_rpowIval hc hNp1R (Ival.mem_sub e1R hsMem))
        (Ival.mem_sub hsMem e1R)
    · -- half term value
      have e0 : ((0 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 0 := Ival.mem_ofRat _ _
      have e0R : (0 : ℝ) ∈ Ival.ofRat c.prec 0 := by exact_mod_cast e0
      have e2 : ((2 : ℚ) : ℝ) ∈ Ival.ofRat c.prec 2 := Ival.mem_ofRat _ _
      have e2R : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by exact_mod_cast e2
      have hexp0 : (0 : ℝ) - s ∈ Ival.sub c.prec (Ival.ofRat c.prec 0) S :=
        Ival.mem_sub e0R hsMem
      rw [zero_sub] at hexp0
      exact Ival.mem_div (mem_rpowIval hc hNp1R hexp0) e2R
  have hfaAll := List.rel_append (List.rel_append (hfaD N) hfaIH) (hfaC M)
  have hsumM := mem_isum c hc _ _ hfaAll
  dsimp only at hsumM
  -- bridge concatenated list sum to analytic `((D + I) + H) + C`
  have hsumEq : ((((List.range N).map (fun k => ((k + 1 : Nat) : ℝ) ^ (-s)))
        ++ [((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1),
          ((N + 1 : Nat) : ℝ) ^ (-s) / 2]
        ++ ((List.range M).map (fun r => emCorr s N (r + 1))))).sum
      = ((Finset.range N).sum (fun k => ((k + 1 : Nat) : ℝ) ^ (-s))
        + ((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1)
        + ((N + 1 : Nat) : ℝ) ^ (-s) / 2)
        + (Finset.range M).sum (fun r => emCorr s N (r + 1)) := by
    simp only [List.sum_append, List.sum_cons, List.sum_nil, add_zero]
    rw [list_sum_map_range, list_sum_map_range]
    ring
  rw [hsumEq] at hsumM
  -- analytic master bound (ported, proved)
  have hmaster := zeta_em_bound hs hs1 hN hM hNM
  -- unfold evaluator, split on tail bound, finish
  simp only [zetaEMIval]
  split
  · rename_i h hiH
    have h2Tle : 2 * emTailScale s N M ≤ h.toReal := by
      have h2 := htailM
      rw [Ival.mem_def, hiH] at h2
      simp only [Ival.leHi_some] at h2
      exact h2.2
    rw [emDirect_eq] at hmaster
    have habs := abs_le.mp hmaster
    have heq : zetaReal s
        = ((Finset.range N).sum (fun k => ((k + 1 : Nat) : ℝ) ^ (-s))
          + ((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1)
          + ((N + 1 : Nat) : ℝ) ^ (-s) / 2
          + (Finset.range M).sum (fun r => emCorr s N (r + 1)))
          + ((riemannZeta (s : ℂ)).re
            - ((Finset.range N).sum (fun k => ((k + 1 : Nat) : ℝ) ^ (-s))
              + ((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1)
              + ((N + 1 : Nat) : ℝ) ^ (-s) / 2
              + (Finset.range M).sum (fun r => emCorr s N (r + 1)))) := by
      unfold zetaReal; ring
    rw [heq]
    rw [Dy.toReal_def] at h2Tle
    refine Ival.mem_add hsumM ?_
    refine Ival.mem_ofRats ?_ ?_ <;>
      (push_cast at habs h2Tle ⊢; linarith [habs.1, habs.2, h2Tle])
  · exact Ival.mem_top _
/-- functional equation for (ported prover proof; handoff `/tmp/zeta_neg_thm.lean`)
`s < 0`, in evaluator association (suggested route:
`riemannZeta_one_sub` at `u = 1 - s`). -/
theorem zeta_neg_fe (s : ℝ) (hs : s < 0) :
    (riemannZeta (s : ℂ)).re
      = ((((2 : ℝ) ^ s * Real.pi ^ (s - 1))
        * Real.sin (Real.pi * s / 2))
        * Real.Gamma (1 - s))
        * (riemannZeta (((1 - s) : ℝ) : ℂ)).re := by
  have hu : (1 : ℝ) < 1 - s := by linarith
  have h1 : ∀ n : ℕ, (((1 - s : ℝ)) : ℂ) ≠ -n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h2 : (((1 - s : ℝ)) : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hfe := riemannZeta_one_sub h1 h2
  have hs' : (1 : ℂ) - (((1 - s : ℝ)) : ℂ) = (s : ℂ) := by push_cast; ring
  rw [hs'] at hfe
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(((1 - s : ℝ)) : ℂ)) = (((2 * Real.pi) ^ (s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  have hcos : Complex.cos (Real.pi * (((1 - s : ℝ)) : ℂ) / 2) = ((Real.sin (Real.pi * s / 2) : ℝ) : ℂ) := by
    rw [← Real.cos_pi_div_two_sub]
    push_cast
    ring_nf
  rw [hfe, hpow, hcos, Complex.Gamma_ofReal]
  have hfac : (2 : ℂ) * (((2 * Real.pi) ^ (s - 1) : ℝ) : ℂ) * ((Real.Gamma (1 - s) : ℝ) : ℂ)
      * ((Real.sin (Real.pi * s / 2) : ℝ) : ℂ)
      = ((((((2 : ℝ) ^ s * Real.pi ^ (s - 1)) * Real.sin (Real.pi * s / 2))
        * Real.Gamma (1 - s)) : ℝ) : ℂ) := by
    rw [Real.mul_rpow (by norm_num) Real.pi_pos.le,
      show (2:ℝ) ^ s = 2 * 2 ^ (s - 1) by
        rw [← Real.rpow_one_add' (by norm_num) (by linarith)]; ring_nf]
    push_cast; ring
  rw [hfac, Complex.re_ofReal_mul]

/-- EM guard: `0 < s ≠ 1` enclosures → Euler–Maclaurin with adaptive `N`;
everything else → `⊤`. -/
def zetaEMGuard (c : Ctx) (X : Ival) (lo hi : Dy) : Ival :=
  if _hpos : 0 < lo.toRat ∧ (hi.toRat < 1 ∨ 1 < lo.toRat) then
    -- `N` adapts to the enclosure size so `s + 2M + 2 ≤ N + 1` is provable
    let M := 4 + c.prec / 8
    let sHi := hi.toRat.num.toNat
    let N := (16 + c.prec / 2) ⊔ (sHi + 2 * M + 2)
    zetaEMIval c X N M
  else Ival.top

/-- positive dispatch: integer points `n ≥ 6` → Euler product;
`0 < s ≠ 1` enclosures → Euler–Maclaurin; everything else → `⊤`.
Non-recursive (the negative branch reuses it for `1 - s > 1`). -/
def zetaPosIval (c : Ctx) (X : Ival) : Ival :=
  match X.lo, X.hi with
  | some lo, some hi =>
    if _hpt : lo = hi then
      if _hnat : lo.toRat.den = 1 ∧ 6 ≤ lo.toRat.num then
        zetaEulerProdIval c lo.toRat.num.toNat (64 + 2 * c.prec)
      else zetaEMGuard c X lo hi
    else zetaEMGuard c X lo hi
  | _, _ => Ival.top

/-- FE factor enclosure for `s < 0`:
`2^s·π^{s-1}·sin(πs/2)·Γ(1-s)·ζ(1-s)` (inner `1-s > 1` reuses the
proved positive dispatch; recursion depth exactly 1). -/
def zetaNegIval (c : Ctx) (X : Ival) : Ival :=
  let A := rpowIval c (Ival.ofRat c.prec 2) X
  let B := rpowIval c c.pi (Ival.sub c.prec X (Ival.ofRat c.prec 1))
  let C := sinIval c
    (Ival.div c.prec (Ival.mul c.prec c.pi X) (Ival.ofRat c.prec 2))
  let oneSub := Ival.sub c.prec (Ival.ofRat c.prec 1) X
  let D := gammaIval c oneSub
  let E := zetaPosIval c oneSub
  Ival.mul c.prec (Ival.mul c.prec (Ival.mul c.prec (Ival.mul c.prec A B) C) D) E

/-- dispatcher: integer points `n ≥ 6` → Euler product; strictly
negative enclosures → functional equation; `0 < s ≠ 1` enclosures →
Euler–Maclaurin; everything else → `⊤`. -/
def zetaIval (c : Ctx) (X : Ival) : Ival :=
  match X.lo, X.hi with
  | some lo, some hi =>
    if _hneg : hi.toRat < 0 then zetaNegIval c X
    else zetaPosIval c X
  | _, _ => Ival.top

theorem zetaPosIval_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (X : Ival)
    (hx : s ∈ X) : zetaReal s ∈ zetaPosIval c X := by
  obtain ⟨hxlo, hxhi⟩ := hx
  cases hlo : X.lo with
  | none =>
    cases hhi : X.hi with
    | none => simp only [zetaPosIval, hlo, hhi]; exact Ival.mem_top _
    | some hi => simp only [zetaPosIval, hlo, hhi]; exact Ival.mem_top _
  | some lo =>
    cases hhi : X.hi with
    | none => simp only [zetaPosIval, hlo, hhi]; exact Ival.mem_top _
    | some hi =>
      have hloR : lo.toReal ≤ s := hxlo lo hlo
      have hhiR : s ≤ hi.toReal := hxhi hi hhi
      rw [Dy.toReal_def] at hloR hhiR
      -- shared EM-guard correctness
      have hem : zetaReal s ∈ zetaEMGuard c X lo hi := by
        simp only [zetaEMGuard]
        split
        · rename_i hpos
          show zetaReal s ∈ zetaEMIval c X
            ((16 + c.prec / 2) ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2))
            (4 + c.prec / 8)
          have hlor : (0 : ℝ) < (lo.toRat : ℝ) := by exact_mod_cast hpos.1
          have hs : 0 < s := lt_of_lt_of_le hlor hloR
          have hs1 : s ≠ 1 := by
            rcases hpos.2 with hlt | hgt
            · have h1 : (hi.toRat : ℝ) < 1 := by exact_mod_cast hlt
              have hlt' : s < 1 := lt_of_le_of_lt hhiR h1
              exact ne_of_lt hlt'
            · have h1 : (1 : ℝ) < (lo.toRat : ℝ) := by exact_mod_cast hgt
              have hgt' : (1 : ℝ) < s := lt_of_lt_of_le h1 hloR
              exact ne_of_gt hgt'
          have hM : 1 ≤ 4 + c.prec / 8 := by omega
          have hN : 1 ≤ (16 + c.prec / 2)
              ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) := by
            have h16 : 1 ≤ 16 + c.prec / 2 := by omega
            exact le_trans h16 le_sup_left
          have hle_q : lo.toRat ≤ hi.toRat := by
            by_contra hlt
            have hlt' : hi.toRat < lo.toRat := not_le.mp hlt
            have hltR : (hi.toRat : ℝ) < (lo.toRat : ℝ) := by
              exact_mod_cast hlt'
            linarith
          have hhi_pos : 0 < hi.toRat := lt_of_lt_of_le hpos.1 hle_q
          have hnn : 0 ≤ hi.toRat.num := by
            have hq : (0 : ℚ) < hi.toRat := hhi_pos
            rw [← hi.toRat.num_div_den] at hq
            have hden : (0 : ℚ) < (hi.toRat.den : ℚ) := by
              have hd := hi.toRat.pos
              exact_mod_cast hd
            rw [div_pos_iff] at hq
            rcases hq with ⟨h, _⟩ | ⟨_, hd⟩
            · have hlt : (0 : ℤ) < hi.toRat.num := by exact_mod_cast h
              exact le_of_lt hlt
            · have hlt : (hi.toRat.den : ℚ) < 0 := hd
              linarith
          have htn : ((hi.toRat.num.toNat : Nat) : ℤ) = hi.toRat.num :=
            Int.toNat_of_nonneg hnn
          have hqi : (hi.toRat : ℝ) ≤ (hi.toRat.num.toNat : ℝ) := by
            have hdiv : (hi.toRat : ℝ)
                = (hi.toRat.num : ℝ) / (hi.toRat.den : ℝ) := by
              conv_lhs => rw [← hi.toRat.num_div_den]
              push_cast
              ring
            rw [hdiv]
            have heq : (hi.toRat.num.toNat : ℝ) = (hi.toRat.num : ℝ) := by
              exact_mod_cast htn
            rw [heq]
            have hnum_nn : (0 : ℝ) ≤ (hi.toRat.num : ℝ) := by
              exact_mod_cast hnn
            have hden_ge : (1 : ℝ) ≤ (hi.toRat.den : ℝ) := by
              have hd1 : 1 ≤ hi.toRat.den := by
                have h := hi.toRat.pos
                omega
              exact_mod_cast hd1
            exact div_le_self hnum_nn hden_ge
          have hsHi : s ≤ (hi.toRat.num.toNat : ℝ) :=
            le_trans hhiR hqi
          have hNM : s + 2 * ((4 + c.prec / 8 : Nat) : ℝ) + 2
              ≤ (((16 + c.prec / 2)
                ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 : Nat) : ℝ) := by
            have hB : ((hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2 : Nat) : ℝ)
                ≤ (((16 + c.prec / 2)
                  ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) : Nat) : ℝ) := by
              exact_mod_cast le_sup_right
            have hcast : ((hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2 : Nat) : ℝ)
                = (hi.toRat.num.toNat : ℝ)
                  + 2 * ((4 + c.prec / 8 : Nat) : ℝ) + 2 := by
              push_cast
              ring
            have hNp1 : (((16 + c.prec / 2)
                ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) : Nat) : ℝ)
                ≤ (((16 + c.prec / 2)
                  ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 : Nat) : ℝ) := by
              have hle : (16 + c.prec / 2)
                  ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2)
                  ≤ (16 + c.prec / 2)
                    ⊔ (hi.toRat.num.toNat + 2 * (4 + c.prec / 8) + 2) + 1 := by
                omega
              exact_mod_cast hle
            linarith
          have hxM : s ∈ X := Ival.mem_def.mpr ⟨hxlo, hxhi⟩
          exact zetaEM_sound c hc s X hxM hs hs1 _ _ hN hM hNM
        · rename_i hnpos
          exact Ival.mem_top _
      simp only [zetaPosIval, hlo, hhi]
      split
      · rename_i hpt
        split
        · rename_i hnat
          have hs_lo : s = (lo.toRat : ℝ) :=
            le_antisymm (by rwa [← hpt] at hhiR) hloR
          have hsq : s = (lo.toRat.num.toNat : ℝ) := by
            have hqeq : lo.toRat = (lo.toRat.num : ℚ) := by
              have h := lo.toRat.num_div_den
              rw [hnat.1] at h
              simpa using h.symm
            have hnn : 0 ≤ lo.toRat.num := by omega
            have htn : ((lo.toRat.num.toNat : Nat) : ℤ) = lo.toRat.num :=
              Int.toNat_of_nonneg hnn
            have hcast : (lo.toRat.num : ℝ) = (lo.toRat.num.toNat : ℝ) := by
              exact_mod_cast htn.symm
            rw [hs_lo, hqeq]
            push_cast
            exact hcast
          have hn : 2 ≤ lo.toRat.num.toNat := by
            have h6 : (6 : ℤ) ≤ lo.toRat.num := hnat.2
            have hnn : 0 ≤ lo.toRat.num := by omega
            have hto : ((lo.toRat.num.toNat : Nat) : ℤ) = lo.toRat.num :=
              Int.toNat_of_nonneg hnn
            have hle : (6 : ℤ) ≤ ((lo.toRat.num.toNat : Nat) : ℤ) := by omega
            have h6n : 6 ≤ lo.toRat.num.toNat := by exact_mod_cast hle
            omega
          have hP : 2 ≤ 64 + 2 * c.prec := by omega
          rw [hsq]
          exact zetaEulerProd_sound c hc _ _ hn hP
        · rename_i hnnat
          exact hem
      · rename_i hpt
        exact hem

theorem zetaNeg_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (X : Ival)
    (hxMem : s ∈ X) (hsneg : s < 0) :
    zetaReal s ∈ zetaNegIval c X := by
  have h2 : (2 : ℝ) ∈ Ival.ofRat c.prec 2 := by
    exact_mod_cast Ival.mem_ofRat c.prec (2 : ℚ)
  have h1 : (1 : ℝ) ∈ Ival.ofRat c.prec 1 := by
    exact_mod_cast Ival.mem_ofRat c.prec (1 : ℚ)
  have hA : (2 : ℝ) ^ s ∈ rpowIval c (Ival.ofRat c.prec 2) X :=
    mem_rpowIval hc h2 hxMem
  have hB : Real.pi ^ (s - 1) ∈ rpowIval c c.pi
      (Ival.sub c.prec X (Ival.ofRat c.prec 1)) :=
    mem_rpowIval hc hc.pi_mem (Ival.mem_sub hxMem h1)
  have hC0 : Real.pi * s / 2 ∈ Ival.div c.prec
      (Ival.mul c.prec c.pi X) (Ival.ofRat c.prec 2) :=
    Ival.mem_div (Ival.mem_mul hc.pi_mem hxMem) h2
  have hC : Real.sin (Real.pi * s / 2) ∈ sinIval c
      (Ival.div c.prec (Ival.mul c.prec c.pi X) (Ival.ofRat c.prec 2)) :=
    mem_sinIval hc hC0
  have h1sub : 1 - s ∈ Ival.sub c.prec (Ival.ofRat c.prec 1) X :=
    Ival.mem_sub h1 hxMem
  have hD : Real.Gamma (1 - s) ∈ gammaIval c
      (Ival.sub c.prec (Ival.ofRat c.prec 1) X) :=
    mem_gammaIval hc h1sub
  have hE : (riemannZeta (((1 - s) : ℝ) : ℂ)).re ∈ zetaPosIval c
      (Ival.sub c.prec (Ival.ofRat c.prec 1) X) :=
    zetaPosIval_sound c hc (1 - s) _ h1sub
  unfold zetaReal
  rw [zeta_neg_fe s hsneg]
  simp only [zetaNegIval]
  exact Ival.mem_mul (Ival.mem_mul (Ival.mem_mul (Ival.mem_mul hA hB) hC) hD) hE

theorem zetaIval_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (X : Ival)
    (hx : s ∈ X) : zetaReal s ∈ zetaIval c X := by
  obtain ⟨hxlo, hxhi⟩ := hx
  cases hlo : X.lo with
  | none =>
    cases hhi : X.hi with
    | none => simp only [zetaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi => simp only [zetaIval, hlo, hhi]; exact Ival.mem_top _
  | some lo =>
    cases hhi : X.hi with
    | none => simp only [zetaIval, hlo, hhi]; exact Ival.mem_top _
    | some hi =>
      have hloR : lo.toReal ≤ s := hxlo lo hlo
      have hhiR : s ≤ hi.toReal := hxhi hi hhi
      rw [Dy.toReal_def] at hloR hhiR
      simp only [zetaIval, hlo, hhi]
      split
      · rename_i hnegH
        have hxM : s ∈ X := Ival.mem_def.mpr ⟨hxlo, hxhi⟩
        have hsneg : s < 0 := by
          have hhir : ((hi.toRat : ℚ) : ℝ) < 0 := by exact_mod_cast hnegH
          linarith
        exact zetaNeg_sound c hc s X hxM hsneg
      · rename_i hnegH
        exact zetaPosIval_sound c hc s X (Ival.mem_def.mpr ⟨hxlo, hxhi⟩)

@[lynth_fn] def zetaR : Fn1 .real .real where
  name := "zeta"
  graph x y := y = zetaReal x
  exu := exu_eq _
  ev c X := zetaIval c X
  sound := fun c x _ X hc hy hx => by
    obtain rfl := hy
    exact zetaIval_sound c hc x X hx
  cost := 400

end Lynth.Interval.Fns
