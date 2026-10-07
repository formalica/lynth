import Lynth.Interval.Fns.Gamma
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
* `s ≤ 0` or `s = 1` (or enclosures touching them) → `⊤` (no negative
  case; the pole is indeterminate).  No complex/Hurwitz/Riemann–Siegel.

Bernoulli numbers reuse `bernoulliQ`/`bernoulliList_getD` (`Fns/Gamma.lean`).
Analytic identities + remainder bounds are `sorry`'d here and mirrored in
`/tmp/zeta_eulerprod_thm.lean`, `/tmp/zeta_em_thm.lean` (Mathlib-only,
for the external prover).
-/

namespace Lynth.Interval.Fns

open BigOperators

/-- real zeta as a real-valued function (graph for the registry entry). -/
noncomputable def zetaReal (s : ℝ) : ℝ := (riemannZeta (s : ℂ)).re

/-- primes `≤ P` (decidable sieve). -/
def primesUpTo (P : Nat) : List Nat := (List.range (P + 1)).filter Nat.Prime

theorem mem_primesUpTo {P p : Nat} : p ∈ primesUpTo P ↔ p.Prime ∧ p ≤ P := by
  simp only [primesUpTo, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨hlt, hp⟩; exact ⟨of_decide_eq_true hp, by omega⟩
  · rintro ⟨hp, hle⟩; exact ⟨by omega, decide_eq_true hp⟩

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

/-- real partial Euler product (mirrors `/tmp/zeta_eulerprod_thm.lean`). -/
noncomputable def eulerProd (n P : Nat) : ℝ :=
  ((primesUpTo P).map fun p => (1 : ℝ) / (1 - 1 / (p ^ n : ℝ))).prod

theorem eulerProd_eq (n P : Nat) :
    eulerProd n P
      = ((primesUpTo P).map fun p => (1 : ℝ) / (1 - 1 / (p ^ n : ℝ))).prod := rfl

/-- SORRY (handoff `/tmp/zeta_eulerprod_thm.lean`): Euler-product tail.
For `2 ≤ n`, `2 ≤ P`,
`|ζ(n) - Π(n,P)| ≤ 2/((P^{n-1})·(n-1))`
(using `Π ≤ ζ(n) ≤ ζ(2) < 2`). -/
theorem zeta_eulerprod_tail (n P : Nat) (hn : 2 ≤ n) (hP : 2 ≤ P) :
    |(riemannZeta (n : ℂ)).re - eulerProd n P|
      ≤ 2 / (((P ^ (n - 1) : Nat) : ℝ) * ((n : ℝ) - 1)) := by
  sorry

/-- Euler-product enclosure at integer `n ≥ 2` (cutoff `P`). -/
def zetaEulerProdIval (c : Ctx) (n P : Nat) : Ival :=
  let ps := primesUpTo P
  let prod := iprod c (ps.map fun p => eulerFactor c n p)
  let E : ℚ := 2 / (((P ^ (n - 1) : Nat) : ℚ) * ((n : ℚ) - 1))
  match prod.lo, prod.hi with
  | some lo, some hi =>
    Ival.ofRats c.prec (lo.toRat - E) (hi.toRat + E)
  | _, _ => Ival.top

theorem zetaEulerProd_sound (c : Ctx) (hc : c.Valid) (n P : Nat) (hn : 2 ≤ n)
    (hP : 2 ≤ P) :
    zetaReal n ∈ zetaEulerProdIval c n P := by
  sorry

/-- one Bernoulli correction
`B_{2r}/(2r)! · rising(s,2r-1)/(N+1)^{s+2r-1}` (all interval ops). -/
def emCorrTerm (c : Ctx) (S Np1 : Ival) (r : Nat) : Ival :=
  let B : ℚ := bernoulliQ (2 * r) / (Nat.factorial (2 * r) : ℚ)
  Ival.div c.prec
    (Ival.mul c.prec (Ival.ofRat c.prec B) (risingIval c.prec S (2 * r - 1)))
    (rpowIval c Np1 (Ival.add c.prec S (Ival.ofRat c.prec ((2 * (r : ℚ)) - 1))))

/-- mirrors `/tmp/zeta_em_thm.lean` (real-valued EM components). -/
noncomputable def emDirectR (s : ℝ) (N : Nat) : ℝ :=
  (Finset.range N).sum fun k => ((k + 1 : Nat) : ℝ) ^ (-s)

noncomputable def emCorrR (s : ℝ) (N r : Nat) : ℝ :=
  (bernoulli (2 * r) : ℝ) / (Nat.factorial (2 * r) : ℝ)
    * (Finset.range (2 * r - 1)).prod (fun j => s + (j : ℝ))
    / ((N + 1 : Nat) : ℝ) ^ (s + (2 * (r : ℝ)) - 1)

noncomputable def emTailScaleR (s : ℝ) (N M : Nat) : ℝ :=
  |(bernoulli (2 * (M + 1)) : ℝ)| / (Nat.factorial (2 * (M + 1)) : ℝ)
    * (Finset.range (2 * (M + 1) - 1)).prod (fun j => s + (j : ℝ))
    / ((N + 1 : Nat) : ℝ) ^ (s + (2 * ((M + 1 : Nat) : ℝ)) - 1)

/-- SORRY (handoff `/tmp/zeta_em_thm.lean`): Euler–Maclaurin identity with
remainder. For `0 < s`, `s ≠ 1`, `1 ≤ N`, `1 ≤ M`,
`(N+1) ≥ s + 2M + 2`:
`|ζ(s) - (D + I + H + Σ corrections)| ≤ 2·T_{M+1}` with the components
as computed by `zetaEMIval`. -/
theorem zeta_em_bound (s : ℝ) (hs : 0 < s) (hs1 : s ≠ 1) {N M : Nat}
    (hN : 1 ≤ N) (hM : 1 ≤ M) (hNM : s + 2 * M + 2 ≤ (N + 1 : Nat)) :
    |(riemannZeta (s : ℂ)).re
      - (emDirectR s N + ((N + 1 : Nat) : ℝ) ^ (1 - s) / (s - 1)
        + ((N + 1 : Nat) : ℝ) ^ (-s) / 2
        + (Finset.range M).sum (fun r => emCorrR s N (r + 1)))|
      ≤ 2 * emTailScaleR s N M := by
  sorry

/-- Euler–Maclaurin enclosure at `S ∋ s` (`0 < s ≠ 1` from the guard). -/
def zetaEMIval (c : Ctx) (S : Ival) (N M : Nat) : Ival :=
  let terms : List Ival := (List.range N).map fun k =>
    Ival.div c.prec (Ival.ofRat c.prec 1)
      (rpowIval c (Ival.ofRat c.prec ((k + 1 : Nat) : ℚ)) S)
  let Np1 := Ival.ofRat c.prec ((N + 1 : Nat) : ℚ)
  let intTerm := Ival.div c.prec
    (rpowIval c Np1 (Ival.sub c.prec (Ival.ofRat c.prec 1) S))
    (Ival.sub c.prec S (Ival.ofRat c.prec 1))
  let halfTerm := Ival.mul c.prec
    (rpowIval c Np1 (Ival.sub c.prec (Ival.ofRat c.prec 0) S))
    (Ival.ofRat c.prec (1 / 2))
  let corrs : List Ival := (List.range M).map fun r => emCorrTerm c S Np1 (r + 1)
  isum c (terms ++ [intTerm, halfTerm] ++ corrs)

theorem zetaEM_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (S : Ival)
    (hsMem : s ∈ S) (hs : 0 < s) (hs1 : s ≠ 1) (N M : Nat) :
    s ∈ zetaEMIval c S N M := by
  sorry

/-- dispatcher: integer points `n ≥ 6` → Euler product; `0 < s ≠ 1`
enclosures → Euler–Maclaurin; everything else → `⊤`. -/
def zetaIval (c : Ctx) (X : Ival) : Ival :=
  match X.lo, X.hi with
  | some lo, some hi =>
    if lo == hi then
      let q := lo.toRat
      if q.den == 1 && 6 ≤ q.num then
        zetaEulerProdIval c q.num.toNat (64 + 2 * c.prec)
      else zetaEMGuard c X lo hi
    else zetaEMGuard c X lo hi
  | _, _ => Ival.top
where
  zetaEMGuard (c : Ctx) (X : Ival) (lo hi : Dy) : Ival :=
    if 0 < lo.toRat && (hi.toRat < 1 || 1 < lo.toRat) then
      zetaEMIval c X (16 + c.prec / 2) (4 + c.prec / 8)
    else Ival.top

theorem zetaIval_sound (c : Ctx) (hc : c.Valid) (s : ℝ) (X : Ival)
    (hx : s ∈ X) : zetaReal s ∈ zetaIval c X := by
  sorry

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
