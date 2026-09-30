# 07 — Integrals (Phase 5): Taylor models and verified quadrature

## 1. Goal shapes (`Goals/Integral.lean`)

* `{x : ℚ // |(∫ y in a..b, f y) - ↑x| < tol}` (interval integral).
* `{x : ℚ // IntegrableOn f (Set.Icc a b) ∧ |(∫ y in Set.Icc a b, f y) - ↑x| < tol}`
  (`IntegralConverges` unfolds to `MeasureTheory.IntegrableOn`).
* `IntegralConvergenceResult f s tol` = `{x // …} ⊕' ¬ …`: left branch when
  `s` is a bounded interval with a bounded integrand (proper integral).
  Improper integrals and divergence proofs are deferred.
* Integrals nested in larger expressions: the `integral` Expr node (03 §5).

Normalization lemmas (simp set `lynth_integral_norm`):
`MeasureTheory.integral_Icc_eq_integral_Ioc`,
`intervalIntegral.integral_of_le` (`∫ in a..b = ∫ in Ioc a b` for `a ≤ b`),
`MeasureTheory.IntegrableOn` on `Icc` ↔ `IntervalIntegrable` (`integrableOn_Icc_iff_integrableOn_Ioc`,
`intervalIntegrable_iff_integrableOn_Icc_of_le`).  The reifier produces the
`integral` node for `intervalIntegral (fun y => body) a b volume`.

## 2. Integrability (proved generically, no external tactic)

`Expr.measurable : Expr t → Bool` — true iff every `Fn` node has `meas = true`
(vars/lits trivially; `sum` of measurable is measurable).

```lean
theorem Expr.measurable_sound (h : e.measurable = true) :
    Measurable (fun y : ℝ => e.denote (ρ.push .real y))
theorem intervalIntegrable_of_bounded (hm : Measurable g) (hB : ∀ y ∈ Set.uIcc a b, g y ∈ I)
    (hI : I.isFinite = true) : IntervalIntegrable g volume a b
```

(`Measurable` + bounded on a finite-measure set ⇒ integrable:
`MeasureTheory.Measure.integrableOn_of_bounded`.)  The boundedness enclosure
`I` is the plain interval evaluation of the body over `[a,b]`, computed by the
checker.  Hence the `IntegrableOn` conjunct of the goal is discharged by the
*same* certificate.

## 3. Taylor models (`Cert/TM.lean`)

```lean
/-- TM on the domain t ∈ [-h, h] around center m (x = m + t):
    ∀ x ∈ [m-h, m+h], f x - Σ coeffs[k] * (x-m)^k ∈ rem -/
structure TM where
  coeffs : Array Dy       -- exact dyadic coefficients (degree ≤ d)
  rem    : Ival
def TM.Valid (T : TM) (m h : Dy) (f : ℝ → ℝ) : Prop :=
  ∀ x, |x - m.toReal| ≤ h.toReal → f x - poly T.coeffs (x - m) ∈ T.rem
```

Operations (degree cap `d`, precision `p`), each with a validity lemma:

| op | rule |
|---|---|
| `const q`, `var` (x = m + t: coeffs `[m, 1]`) | exact (rounding of `m` into rem if needed) |
| `add`, `neg`, `sub`, `smul` | coefficient-wise, rounding errors swept into `rem` |
| `mul` | convolve; terms of degree > d bounded by `|t|^k ≤ h^k` into `rem`; plus `P₁R₂ + P₂R₁ + R₁R₂` bounded with `bound(P)` |
| `bound T` | interval of `poly(t) + rem` over `t ∈ [-h,h]` (interval Horner on `[-h,h]`; optionally Bernstein, vendored from LeanCert) |
| `compose F T` | see §4 |
| `integrate T` | `∫_{-h}^{h} poly = Σ_{k even} c_k · 2h^{k+1}/(k+1)` exactly (dyadic up to division by k+1 → rounded interval), plus `2h · rem` |

Validity lemmas are the standard Taylor-model lemmas; LeanCert has proofs for
`Polynomial ℚ`-based TMs (`Engine/TaylorModel/Core.lean`: `add_evalSet_correct`,
`mul_evalSet_correct`, `foil_to_trunc_remainder`) and a computable dyadic
version (`Engine/CompPoly.lean`: `DyPoly`, `DyTM`).  Vendor `CompPoly.lean`
and re-prove validity against our `TM.Valid` (list-based polynomial
`poly cs t = Σ cs[k] t^k`, with lemmas `poly_add`, `poly_mul_trunc`).

## 4. Per-function Taylor capability (`TayCap`)

For `F : ℝ → ℝ` (and later `ℂ → ℂ`, see 10 §4):

```lean
structure TayCap1 where
  /-- given a dyadic center c, a range V ∋ 0 of the perturbation and degree d,
      return dyadic coefficients a₀..a_d and an error interval E with
      ∀ v ∈ V, F (c + v) - Σ a_k v^k ∈ E -/
  expand : Ctx → (c : Dy) → (V : Ival) → (d : Nat) → Array Dy × Ival
  expand_ok : ∀ ctx c V d v, ctx.Valid → v ∈ V → F (c + v) - poly (expand …).1 v ∈ (expand …).2
```

Generic recipe to implement `expand` for a function with known derivatives:
1. enclosures `A_k ∋ F^{(k)}(c)/k!` for `k ≤ d` (point kernels);
2. enclosure `D ∋ F^{(d+1)}(ξ)/(d+1)!` for all `ξ ∈ c + V` (interval kernels);
3. `a_k := mid A_k`; `E := Σ_k (A_k - a_k)·V^k + D·V^{d+1}` (interval arithmetic).
Soundness from Taylor's theorem with Lagrange remainder
(`taylor_mean_remainder_lagrange`, needs `ContDiffOn ℝ (d+1) F`) plus formulas
for `iteratedDeriv`.  Provide per function:

| F | k-th Taylor coefficient at c | derivative facts |
|---|---|---|
| exp | `exp c / k!` | `iteratedDeriv_exp` (derive from `Real.deriv_exp`) |
| sin, cos | `±sin c / k!`, `±cos c / k!` cyclic | `Real.iteratedDeriv_sin/cos` (prove by induction from `Real.deriv_sin`) |
| log (c>0) | `(-1)^{k+1} / (k c^k)`, `k ≥ 1` | via `deriv log = inv` and `iteratedDeriv` of `zpow` |
| sqrt, x^r (c>0) | binomial `C(r,k) c^{r-k}` | `Real.rpow` derivatives |
| inv (c≠0) | `(-1)^k / c^{k+1}` | |
| arctan | via `arctan(c + v) = arctan c + arctan (v / (1 + c² + c v))` (TM division + odd series) | `Real.arctan_add` |

Then `TM.compose F T`: let `c := T.coeffs[0]`, `S := T - c` (no constant
term), `V := bound S`; `(a, E) := F.tay.expand ctx c V d`;
result `:= Σ_k a_k · S^k (TM powers, Horner) + E` (E added to rem).

Composite-expression TM: `Expr.tm (c : Ctx) (d : Nat) (m h : Dy) : Expr .real → IEnv → TM`
by structural recursion; nodes without `tay` capability → TM with
`rem := Expr.eval` of the node on the whole piece and zero polynomial (sound,
low order).  Soundness theorem:

```lean
theorem Expr.tm_valid (hc : c.Valid) (hσ) (e : Expr .real) :
    (e.tm c d m h σ).Valid m h (fun x => e.denote (ρ.push .real x))
```

## 5. Quadrature certificate (`Cert/Integral.lean`)

```lean
structure QuadCfg where
  pieces : List Dy   -- partition points a = x₀ < x₁ < … < x_n = b (dyadic, inner points only)
  deg    : Nat
def Quad.eval (c : Ctx) (t : Ty) (A B : Ival) (body : Expr t) (σ : IEnv) (q : QuadCfg) : t.Enc
```

For real `t`: if `A`, `B` are points (typical) use the partition
`[A] ++ q.pieces ++ [B]`; on each piece `[x_i, x_{i+1}]` with center `m`,
half-width `h`: `TM := body.tm c q.deg m h (σ.push .real X_piece)`; add
`TM.integrate`.  Endpoints that are not exact dyadics (e.g. `π`): split off
the end pieces `[B.lo, B.hi]` and bound their contribution by
`width · eval(body over [B.lo, B.hi])` with sign handling (signed integral
`∫_a^b` = `-∫_b^a`); proof via `intervalIntegral.integral_add_adjacent_intervals`.
If `body.measurable = false` or some piece enclosure is infinite → `Ty.top`.

Soundness: `Quad.eval_sound` uses (1) additivity over the partition,
(2) `intervalIntegral.integral_mono_on` / `norm_integral_le_of_norm_le` for
`∫ (f - poly) ∈ 2h·rem`, (3) exact polynomial integral
(`integral_pow`, `intervalIntegral.integral_comp_sub_right`),
(4) integrability from §2.

Native search: adaptive bisection of `[a,b]` until each piece's TM remainder
contribution `≤ tol_share`; degree `d ∈ {4, 8, 12}` chosen to minimize cost.
The resulting partition is stored in the `integral` node (`QuadCfg`), so the
checker recomputes the same TMs.

Complex-valued integrands (`t = cplx`): integrate real and imaginary parts
with complex TMs (pairs of TMs) — see 10 §4.

## 6. Expected performance

`∫₀^{2π} exp(cos θ)` to `1e-5` with degree 8: ≈ 16 pieces.  Narrow Gaussian
`exp(-1000(x-1/2)²)` on `[-1,1]`: adaptive pieces concentrate near `1/2`,
≈ 40 pieces.  Kernel checks should stay < 30 s; otherwise `auto` → native.

## 7. Milestone

* **M9** TM core + exp/sin/cos/log/sqrt/inv/pow Taylor capabilities.
* **M10** quadrature + integrability: `Integrals.lean` T15–T17,
  `ImproperIntegrals.lean` IC01–IC03, IC08 (IC09 10-D cube deferred unless
  simple: Fubini over boxes is out of scope).
