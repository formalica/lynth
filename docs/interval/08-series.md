# 08 — Infinite sums (Phase 6)

## 1. Goal shapes (`Goals/Series.lean`)

* `{x : ℚ // Summable f ∧ |tsum f - ↑x| < tol}` (also `∑' k, f k`).
* `SeriesSummabilityResult f tol = {x // Summable f ∧ …} ⊕' ¬ Summable f`.
* `¬ Summable f`.
* `f` is a user definition `f : ℕ → ℝ` (unfold) or a lambda; complex-valued
  series `f : ℕ → ℂ` analogous with norms (10 §5).
* tsum/Summable nested in larger expressions: not supported in the `Expr` AST
  (handled only at goal level).

## 2. Idea: asymptotic enclosures on `[N, ∞)`

A tail certificate needs bounds valid **for all** `k ≥ N` — infinitely many
indices, so plain interval evaluation is not enough.  We use an *asymptotic
interval arithmetic* (AIA) whose values describe the whole tail at once.

```lean
/-- ∀ k ≥ N, f k ∈ r^k · k^α · I   (r ≥ 0 dyadic, α rational, I interval) -/
structure Asy where
  r     : Dy        -- geometric base, r ≥ 0
  alpha : ℚ         -- power exponent (small rationals: integers and halves)
  I     : Ival      -- bounded factor
def Asy.Valid (N : ℕ) (f : ℕ → ℝ) (A : Asy) : Prop :=
  ∀ k ≥ N, ∃ v ∈ A.I, f k = (A.r.toReal) ^ k * (k : ℝ) ^ (A.alpha : ℝ) * v
```

(`N ≥ 1` so `k^α` is harmless.)  Operations with validity lemmas (all
elementary inequalities for `k ≥ N`):

| op | rule |
|---|---|
| `natCast k` | `r=1, α=1, I=[1,1]` |
| `const q` | `r=1, α=0, I=ofRat q` |
| `k + a` (a ≥ 0 const) | `α=1, I=[1, 1 + a/N]` ; negative `a`: `[1 + a/N, 1]` if `N > |a|` |
| `mul` | `r₁r₂`, `α₁+α₂`, `I₁·I₂` |
| `add` (same r) | `α := max`, `I := I_max + N^{α_min-α_max}·[0,1]·I_min` (sign-aware: the factor `k^{α_min-α_max} ∈ (0, N^{α_min-α_max}]`) |
| `add` (different r, r₂ < r₁) | `(r₂/r₁)^k k^{α₂-α₁} ≤ (r₂/r₁)^N N^{…}` bound when monotone decreasing (check `α₂-α₁ ≤ 0` or ratio test `(r₂/r₁)·((N+1)/N)^{α₂-α₁} ≤ 1`) |
| `inv` | `r ↦ 1/r` (division rounded), `α ↦ -α`, `I ↦ I⁻¹` (requires `0 ∉ I`) |
| `npow` by const n | `r^n, nα, I^n` |
| `rpow (base, const s)` base with `r = 1`, `I > 0` | `α·s`, `I^s` |
| `c ^ k` (const base, index exponent) | `r := |c|`, sign factor `I := [-1,1]` if `c < 0` (exact sign alternation is *not* tracked; only magnitudes matter for summability) |
| `k ^ k`-like (`rpow` with index exponent, base `≥ k+1`) | bound by geometric `r := 1/(N+1)` (valid for `k ≥ N`: `(k+1)^{-(k+1)} ≤ (N+1)^{-(k+1)}`) |
| `Nat.factorial (k + a)` (in a denominator) | `1/(k+a)! ≤ (1/(N+a)!) · (N+a+1)^{-(k-N)}` ⇒ geometric `r := 1/(N+a+1)` |
| `Nat.fib (k + a)` | Binet `Real.coe_fib_eq : (Nat.fib n : ℝ) = (φ^n - ψ^n)/√5`: `r := φ` (enclosure of the golden ratio), `I` from `|ψ/φ|^N` |
| `exp(-k)`, `exp(c·k)` | `r := exp(c)` (enclosure; take upper for upper bounds: represent `r` as an interval `R` if needed) |

Functions register AIA behaviour through an optional capability
`asy : Option (AsyCap)` on `Fn1`; the table above lists the built-ins.

## 3. Tail bounds and summability (`Cert/Tail.lean`)

For a valid `A` on `[N, ∞)` with `M := max |I|`:
* `r < 1`: `Σ_{k≥N} |f k| ≤ M · Σ_{k≥N} r^k k^α` ≤ geometric bound: if `α ≤ 0`
  then `≤ M r^N / (1 - r)`; if `α > 0` use `k^α r^k ≤ N^α r^N · q^{k-N}` with
  `q := r·((N+1)/N)^α < 1` (checked).  Summable by `Summable.of_norm_bounded`.
* `r = 1`, `α < -1`: p-series: `Σ_{k≥N} k^α ≤ N^α + ∫_N^∞ x^α dx =
  N^α + N^{α+1}/(-α-1)` (`AntitoneOn.sum_le_integral`,
  `integral_Ioi_rpow_of_lt`); summable by `Real.summable_nat_rpow`.
* `r = 1`, `α ≥ -1`, `I ⊆ (0, ∞)` or `I ⊆ (-∞, 0)` (sign-definite *in
  absolute value*: use AIA of `|f|`): **not summable** by comparison with the
  harmonic series (`Real.not_summable_natCast_inv`, `Summable.of_nonneg_of_le`
  contrapositive, `summable_abs_iff`).
* `r > 1` with `I ∌ 0`: not summable (terms don't tend to 0).

The value: `tsum f = Σ_{k<N} f k + tail`, `tail ∈ [-T, T]` with `T` the bound
above; `Σ_{k<N}` via the `sum` node evaluator.  Certificate:

```lean
structure SeriesCert where
  N    : Nat
  prec : Nat
  -- body : Expr .real with nat var 0 (reified f k)
def checkSeries (c : Ctx) (body : Expr .real) (N : Nat) (tol : Ival) (q : ℚ) : Bool :=
  let A := body.asy c N            -- Asy on [N, ∞)
  let T := tailBound A N           -- Option Dy
  let S := (Expr.sum .real (natLit N) body).eval c IEnv.nil
  -- |S ± T - q| < tol.lo
theorem checkSeries_sound : checkSeries … = true → Summable f ∧ |tsum f - q| < tol
```

## 4. Sharper tails (to keep N small)

Slowly converging tails (`1/k²`: N ≈ 10^5 for 1e-5 with the crude bound) use
two-sided *integral-test* enclosures for monotone positive terms:
`∫_N^∞ g ≤ Σ_{k≥N} g(k) ≤ g(N) + ∫_N^∞ g` for antitone `g` on `[N, ∞)` with
closed-form `∫` (power functions `c·(k+a)^α`: `integral_Ioi_rpow_of_lt`).
The tail interval then has width ≈ `g(N)`; refine with the AIA factor `I`.
This gives N ≈ 300–3000 for the tests; acceptable natively and in the
kernel (≈1–10 s).  (Euler–Maclaurin corrections are a later optimization.)

Monotonicity of `g` on `[N, ∞)` is certified by the AD evaluator on the
extended interval `[N, +∞]` (06 §5) with `k` relaxed to a real variable —
possible when the body only uses functions defined for real arguments
(`natCast k` relaxes to the real variable; `Nat.factorial`/`Nat.fib` do not).

## 5. Alternating series

`Summable` in Lean is absolute summability for ℝ, so
`∑ (-1)^k/(k+1)` is **not summable** (`tsum = 0` by convention).  The AIA of
`|f|` gives `α = -1, I > 0` ⇒ `¬ Summable` (right branch).  For absolutely
summable alternating series (`(-1)^(k+1)/(k+1)^2`) the magnitude tail bound
works; optionally a sharper alternating-tail bound (`|tail| ≤ |f N|` for
decreasing magnitudes: `Antitone.alternating_series_le_tendsto` family) can be
added.

## 6. Milestone

* **M11** AIA + tails: `InfiniteSums.lean` IS01–IS13 (IS07 via the integral
  test), both `_not_summable` theorems, `Sums.lean` B01 (already closed form).
