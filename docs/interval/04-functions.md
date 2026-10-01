# 04 — Function implementations (Phase 2)

Every function is a registry entry (`03 §9`).  This file fixes the algorithm,
the soundness argument and the Mathlib lemmas for each.  `p = c.prec`;
`w = p + guard` is the internal working precision (guard bits documented per
function).  All point kernels work on dyadic points; interval extensions are
derived by monotonicity / critical-point analysis.

## 0. Shared toolkit (`Series/Horner.lean`, `Series/Tail.lean`)

```lean
/-- interval Horner: coefficients as intervals, argument interval -/
def hornerI (p : Nat) (cs : List Ival) (X : Ival) : Ival :=
  cs.foldr (fun C acc => Ival.add p C (Ival.mul p X acc)) (Ival.pt 0)
theorem mem_hornerI (hcs : List.Forall₂ (fun a C => a ∈ C) as cs) (hx : x ∈ X) :
    (as.reverse… Σ aᵢ xⁱ) ∈ hornerI p cs X                  -- FTIA by induction

/-- value = polynomial part + remainder with |rem| ≤ R -/
theorem mem_poly_add_rem {v P R : ℝ} {I : Ival} {Rd : Dy}
    (hP : P ∈ I) (hR : |v - P| ≤ Rd.toReal) : v ∈ I.widen p Rd   -- [lo - R, hi + R]

/-- geometric tail: HasSum f s, |f k| ≤ C q^k for k ≥ N, 0 ≤ q < 1 -/
theorem abs_sub_partial_le_geom (hs : HasSum f s) (hb : ∀ k ≥ N, |f k| ≤ C * q ^ k) (hq0 hq1) :
    |s - ∑ k ∈ range N, f k| ≤ C * q ^ N / (1 - q)
```

Coefficient intervals such as `1/k!` are produced exactly as dyadic intervals
by `Ival.ofRat p (1 / k!)` or incrementally (`c_{k+1} = c_k / (k+1)` with
`divDown/divUp`).

## 1. Arithmetic (`Fns/Arith.lean`)

| pattern | record | ev |
|---|---|---|
| `?x + ?y`, `?x - ?y`, `?x * ?y`, `-?x`, `?x / ?y`, `?x⁻¹` (ℝ) | `Fn2 .real .real .real` / `Fn1` | `Ival.add/sub/mul/neg/div/inv` |
| same on ℂ | `.cplx` versions | `CBox.*` |
| `?x ^ (?n : ℕ)` (ℝ, ℂ) | `Fn2 t .nat t` | `npow` when `n` is a point, else ⊤ (ℝ: if base ⊆ [0,1] or [1,∞) use monotonicity in n) |
| `?x ^ (?n : ℤ)` | `Fn2 .real .real …` via exact `n` | `npow` / `inv ∘ npow` |
| `|?x|`, `max`, `min` | `Fn1`/`Fn2` | `Ival.abs/max/min` |
| `((?n : ℕ) : ℝ)`, `((?n:ℕ):ℂ)`, `((?x:ℝ):ℂ)` | casts | `NIval.toIval`, `CBox.ofReal` |
| `?n + ?m`, `?n * ?m`, `?n + 1`, `?n - ?m` (ℕ) | `.nat` records | `NIval` ops |
| `Nat.factorial ?n`, `Nat.fib ?n`, `Nat.choose ?n ?k`, `2 ^ ?n` (ℕ) | `.nat` | monotone lift / exact at points |

`(-1 : ℝ) ^ k` needs no special case: `npow` of the point `[-1,-1]` with a
point exponent is exact.

## 2. Constants (`Fns/Const.lean`)

**π** (`piIval p`): Machin, `Real.four_mul_arctan_inv_5_sub_arctan_inv_239 :
4 * arctan 5⁻¹ - arctan 239⁻¹ = π / 4`.  `arctan` of small rationals by the
alternating series with tail `|x|^(2N+1)/(2N+1)` (see §6).  N from `w`.
Guard: 8 bits.  Also expose `Fn0 .real` "pi" with pattern `Real.pi`, whose
`ev c := c.pi`.

**log 2** (`ln2Ival p`): `log 2 = 2·artanh(1/3)`; via
`Real.hasSum_log_sub_log_of_abs_lt_one (x := 1/3)` :
`HasSum (fun k => 2 * (1/(2k+1)) * x^(2k+1)) (log (1+x) - log (1-x))`
and the geometric tail (ratio `x² = 1/9`).

`Real.exp 1` needs no constant (it is `exp` of a literal).

## 3. exp (`Fns/Exp.lean`)

Point kernel `expPt (w) (a : Dy) : Ival` (sound: `exp a ∈ expPt w a`):
1. `s := max 0 (bitExp(a) + 10)` so that `r := a / 2^s` (exact `scale2`)
   satisfies `|r| ≤ 2^-10`.
2. `N := w / 10 + 2` terms; `P := hornerI w [1, 1, 1/2!, …, 1/(N-1)!] (pt r)`.
3. remainder `R := |r|^N · (N+1)/(N!·N)` rounded up (`Real.exp_bound :
   |x| ≤ 1 → 0 < n → |exp x - ∑ i ∈ range n, x^i/i!| ≤ |x|^n * (n.succ / (n! * n))`).
4. `E := (P.widen R).clampLo 0` (sound because `exp > 0`).
5. square `s` times with `Ival.sq` at precision `w` (monotone on nonneg;
   `Real.exp_nat_mul : exp (n * x) = exp x ^ n` with `n = 2^s`, or iterate
   `exp (2y) = exp y ^ 2`).
6. Guard bits: `w = p + s + 16`.

Interval extension: monotone (`Real.exp_le_exp`):
`expIval c X = ⟨X.lo.map (lo ∘ expPt), X.hi.map (hi ∘ expPt)⟩` with
`lo = -∞ ↦ some 0` (exp > 0) and `hi = +∞ ↦ none`.

Capabilities: `meas` (`Real.measurable_exp`), `cont` (always true), `dev`
(derivative = exp itself: `Real.hasDerivAt_exp`, enclosure `expIval c X`),
`conv` (everywhere; see 09), `tay` (coefficients `exp(c)/k!`, remainder
`exp(c+V)/(d+1)!·V^(d+1)`; see 07).

## 4. log (`Fns/Log.lean`)

Point kernel for dyadic `a > 0`:
1. `k := round(log₂ a)` from `bits`, `t := a / 2^k ∈ [2/3, 4/3]` (exact).
2. `z := (t-1)/(t+1)` as an **interval** `Z` (division rounded), `|z| ≤ 1/5`.
3. `log t = 2·Σ z^(2j+1)/(2j+1)` (`Real.hasSum_log_sub_log_of_abs_lt_one` with
   `log((1+z)/(1-z)) = log t` since `(1+z)/(1-z) = t`); series by
   `hornerI` in `Z²` times `Z`; tail `2|z|^(2N+1)/((2N+1)(1-z²))` with `|z|`
   from `Z`'s magnitude.
4. `log a = k·ln2 + log t` using `c.ln2` (`Real.log_mul`, `Real.log_zpow`).

Interval extension: if `X.lo > 0`: monotone (`Real.log_le_log`) with
`hi = +∞ ↦ none`; else `⊤` (Mathlib's `log x = log |x|`, `log 0 = 0` are not
worth modelling).  `dev`: `1/x` on `X ⊆ (0,∞)` (`Real.hasDerivAt_log`).
`cont`: `X.lo > 0` or `X.hi < 0`.

## 5. sqrt (`Fns/Sqrt.lean`)

`sqrtIval c X = ⟨X.lo.map (fun l => if l ≤ 0 then 0 else sqrtDown w l),
X.hi.map (fun h => if h ≤ 0 then 0 else sqrtUp w h)⟩` with `-∞ ↦ some 0`.
Mathlib: `Real.sqrt_le_sqrt`, `Real.sqrt_eq_zero'`, `Real.sqrt_nonneg`;
kernels vendored from LeanCert (`sqrtRatLowerPrec_le_sqrt`,
`sqrt_le_sqrtRatUpperPrec`).  `dev`: `1/(2√x)` on `X.lo > 0`.

## 6. arctan (`Fns/Arctan.lean`)

Point kernel `atanPt w a` (monotone ⇒ interval by endpoints; `-∞ ↦ -π/2`,
`+∞ ↦ π/2` using `c.pi`; `Real.arctan_lt_pi_div_two`, `Real.neg_pi_div_two_lt_arctan`):
1. Sign symmetry `arctan (-x) = - arctan x` (`Real.arctan_neg`).
2. If `a > 1`: `arctan a = π/2 - arctan (1/a)` (`Real.arctan_inv_of_pos`), with
   `1/a` as an interval → use interval kernel below on `[1/a]`.
3. For `0 ≤ x ≤ 1`: two argument halvings
   `arctan x = 2·arctan (x / (1 + √(1+x²)))` (prove from `Real.tan_arctan`,
   `Real.cos_arctan`, `Real.sin_arctan` + half-angle; ~40 lines) giving
   `|z| ≤ tan(π/16) < 0.2`.
4. Series `Σ (-1)^j z^(2j+1)/(2j+1)` with tail `|z|^(2N+1)/(2N+1)` (alternating;
   derive the real series from `Complex.hasSum_arctan`/`Real.arctan`'s
   derivative, or prove the remainder bound directly:
   `|arctan z - Σ_{j<N} …| ≤ |z|^(2N+1)/(2N+1)` by the integral of the
   geometric remainder `t^(2N)/(1+t²) ≤ t^(2N)`).
Because the halving uses `√` and `/`, the kernel works on intervals `Z`; the
series is evaluated with `hornerI` on `Z²`.

## 7. sin / cos (`Fns/Trig.lean`)

Point kernels for dyadic `y` with `|y| ≤ 1`: via the complex exponential bound
`Complex.exp_bound (hx : ‖x‖ ≤ 1) (hn : 0 < n) : ‖exp x - Σ_{m<n} x^m/m!‖ ≤ ‖x‖^n * (n.succ / (n! * n))`
at `x = y·I`, take real/imag parts: `cos y`, `sin y` each within that bound of
the even/odd partial sums.  Evaluate partial sums with `hornerI` in `y²`.

Interval extension `sinIval c X` (cos analogous, or `cos x = sin (x + π/2)`
via `Real.sin_add_pi_div_two`):
1. If `X` infinite or `width X ≥ 4` → `[-1, 1]` (`Real.sin_le_one`, `Real.neg_one_le_sin`).
2. `k := round (mid X · 2/π)` (float/dyadic heuristic, any integer is sound);
   `Y := X - k·(π/2)` as an interval using `c.pi` (sound for every `k`).
3. `sin x = sgn·(sin|cos) y` according to `k mod 4`
   (`Real.sin_add_pi_div_two`, `Real.sin_add_pi`, `Real.sin_add_two_pi`,
   `Real.sin_add_int_mul_two_pi` — prove one lemma
   `sin (y + k * (π/2)) = [sin y, cos y, -sin y, -cos y][k % 4]`).
4. If `Y ⊆ [-π/2, π/2]` (certified with `c.pi`), use monotonicity of `sin`
   (`Real.strictMonoOn_sin`) on the endpoints of `Y` (point kernels, which need
   `|y| ≤ 1`: for `1 < |y| ≤ π/2` use one halving `sin 2u = 2 sin u cos u`,
   `cos 2u = 1 - 2 sin² u`), and for `cos` on `Y`: even function, antitone on
   `[0, π]` (`Real.strictAntiOn_cos`), max `1` if `0 ∈ Y`.
5. Otherwise Lipschitz fallback: `sin x ∈ sin m ± r ∩ [-1,1]`
   (`Real.abs_sin_sub_sin_le`, analogous `abs_cos_sub_cos_le`) where `m` is the
   midpoint and `r` the radius.
`dev`: cos / -sin enclosures.  `tay`: cyclic derivatives.

## 8. tan, cot, sec… (derived, `Fns/Trig.lean`)

`tan x = sin x / cos x` (`Real.tan_eq_sin_div_cos`), `cot x = cos x / sin x`
(`Real.cot_eq_cos_div_sin`).  Use `Fn1.ofExpr` so soundness is automatic;
division by an interval containing 0 gives ⊤ (sound since Mathlib `x/0 = 0`
is inside ⊤).

## 9. arcsin, arccos (`Fns/InvTrig.lean`)

`arcsin x = arctan (x / √(1 - x²))` for `x ∈ (-1,1)` (`Real.arcsin_eq_arctan`);
`arcsin` is monotone on ℝ (clamped: `Real.arcsin_of_one_le`,
`Real.arcsin_of_le_neg_one`, `Real.arcsin_le_arcsin`).  Point kernel for
`|a| < 1` via the identity; `a ≥ 1 ↦ π/2`, `a ≤ -1 ↦ -π/2`.
`arccos x = π/2 - arcsin x` (`Real.arccos_eq_pi_div_two_sub_arcsin`).

## 10. Hyperbolic (`Fns/Hyperbolic.lean`)

* `sinh x = (exp x - exp (-x))/2` (`Real.sinh_eq`), strictly monotone
  (`Real.sinh_strictMono`): endpoints.  For `|a| < 2^-8` use the odd Taylor
  series (avoid cancellation) — optional optimization.
* `cosh x = (exp x + exp (-x))/2` (`Real.cosh_eq`), even, monotone on `[0,∞)`
  (`Real.cosh_le_cosh : cosh x ≤ cosh y ↔ |x| ≤ |y|`): `[cosh(min|X|), cosh(max|X|)]`.
* `tanh x = sinh x / cosh x`; monotone (prove `StrictMono Real.tanh` from
  derivative `1/cosh²` or from `tanh x = 1 - 2/(exp(2x)+1)`): endpoints with
  `tanh a = 1 - 2/(exp(2a)+1)` evaluated with directed rounding; ±∞ ↦ ±1.
* `arsinh x = log (x + √(1+x²))` (Mathlib definition, `Real.arsinh`), monotone
  (`Real.arsinh_strictMono`); for `a < 0` use `arsinh (-x) = -arsinh x`.
* `arcosh`, `artanh`: use the Mathlib definitions (`Real.arcosh`,
  `Real.artanh` in `Mathlib/Analysis/SpecialFunctions/Arcosh.lean`,
  `Artanh.lean`) — unfold with `Fn1.ofExpr` using their defining identity;
  monotone on their domains; outside the domain return ⊤.

## 11. Powers and logarithms with other bases (`Fns/Pow.lean`)

* `x ^ (y : ℝ)` (`Real.rpow`): if `X.lo > 0`: `exp (Y · log X)`
  (`Real.rpow_def_of_pos : 0 < x → x ^ y = exp (log x * y)`), interval ops.
  If `Y` is the exact point `m/2` (common) optionally `√x^m`.  If `X` contains
  0 or negatives → ⊤ (unless `Y` is an exact natural number: use `npow` via
  `Real.rpow_natCast`).
* `Real.logb b x = log x / log b` (definitionally `Real.logb`; `Fn2` via
  `ofExpr`).
* `Real.sqrt` handled in §5; `x ^ (1/3 : ℝ)` goes through rpow.

## 12. sinc (`Fns/Sinc.lean`)

`Real.sinc x = if x = 0 then 1 else sin x / x`.
* If `0 ∉ X`: `sin(X) / X` (division).
* If `0 ∈ X` and `|X| ≤ 1`: `[1 - M²/6, 1]` with `M = max|X|`
  (`sin x ≥ x - x³/6` for `x ≥ 0`: `Real.sin_bound` or
  `Real.sin_gt_sub_cube`; `Real.sinc_le_one`).
* Else `[-1, 1]` (`Real.abs_sinc_le_one`).

## 13. ℕ-valued functions (`Fns/Nat.lean`)

`Nat.factorial`, `Nat.fib`, `Nat.choose n k` (k fixed point), `2^n`, `n+1`,
`n*m`: `NIval` monotone lifts (`Nat.factorial_le`, `Nat.fib_mono`,
`Nat.pow_le_pow_right`).  All are exact on points.  Casting to ℝ is exact.

## 14. Complex functions

See `10-complex.md` §2 (exp, log, sin, cos, sinh, cosh, cpow, sqrt, arg,
norm, re, im, conj, ofReal, I).

## 15. Deferred (registered later, `12-tests.md` "deferred")

`riemannZeta`, `Real.eulerMascheroniConstant`,
`Complex.digamma`, `NNReal.agm`, hypergeometric functions, `Real.erf`.  The
reifier must fail on them with a clear message ("no registry entry for
…") so the tests report cleanly.  Recommended algorithms are kept in
`13-progress.md §Deferred notes` (zeta: partial sums +
integral tail; γ: `eulerMascheroniSeq` bounds; agm: `agmSequences` bounds).

`Real.Gamma` is **not** deferred anymore: see §17.

## 16. Performance targets (M3 acceptance)

Native: point enclosure of any Compositions test at 128 bits < 5 ms.
Kernel (`decide +kernel`): any Basic/Compositions test < 15 s.

## 17. Gamma (`Fns/Gamma.lean`)

Stirling expansion of `log Γ` with shifting and reflection (FLINT/Arb
`arb_hypgeom_gamma` design — this **replaces** the incomplete-gamma plan
from `13-progress.md §Deferred notes`, which needs 120+ `exp`/`log`
evaluations per point and loses ~37 bits to cancellation at `X = 40`;
Stirling needs ~60 interval ops and closes the Gamma tests at `prec = 64`).

* `stirlingCoeff k = B_{2k}/(2k(2k-1))`, `k = 1..24`, as `ℚ` literals
  (`decide` cannot evaluate Mathlib `bernoulli`: well-founded recursion).
* `gammaShift a T`: least `r` with `a + r ≥ T`, `T = max(10, w/8)`.
* `risingIval`: `x(x+1)…(x+r-1)`; identity `Γ(x) = Γ(x+r)/rising` holds
  **universally** (division form: at poles both sides are `0` via Mathlib's
  `Γ = 0` at nonpositive integers and `_/0 = 0`).
* `stirlingAcc`: Horner in `z⁻²` of `Σ_{k<N} c_k z^{-(2k-1)}`
  (`N ≤ 24`, chosen adaptively by `chooseN` against `2^{-(w+8)}` —
  pure computation, any `N` is sound).
* tail `2|c_N|/z^{2N-1}` via `npow`/`div`, `widenMag`/`magHi`.
* `gammaPosIval`: shift + Stirling `log Γ` + `expIval` + rising division.
  Sound for **every** `X` (tight for positive/narrow); the Stirling
  identity+remainder on `[8, ∞)` is the temporary axiom
  `stirling_logGamma` (FLINT's real bound, constant `2`).
* `gammaReflIval`: `Γ(x) = (π/sin(πx))/Γ(1-x)` for `hi < 1`
  (`Real.Gamma_mul_Gamma_one_sub`); division form fails at positive
  integers, hence the `hi < 1` restriction.
* `gammaIval`: positive fast path, reflection below `1`, else
  `hull` of the `(-∞, 0]`/`[0, ∞)` pieces.  No monotonicity analysis:
  wide positive intervals are sound but coarse (subdivision recovers
  them); all current Gamma tests are points.
* Precision behavior: ~60 good bits at `prec = 64`, ~174 bits at
  `prec = 256` (then the `N ≤ 24` table caps the tail, still sound).
