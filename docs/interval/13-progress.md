# 13 — Progress (living document)

Update at every milestone.  Keep "Next" pointing at the lowest unfinished item.

## Milestones

| id | content | status |
|---|---|---|
| M0 | spec (`docs/interval/*`), test statement fixes | in progress |
| M1 | `Num/`: vendored Dyadic, `Dy` rounding ops, `Ival`, `NIval`, `CBox` + proofs | todo |
| M2 | `Core/`: Ty, Ctx, Fn records, Env, Expr, denote, eval, eval_sound, PropExpr | todo |
| M3 | Registry attribute, reifier, exact evaluator, trust driver, Approx + Closed handlers; arithmetic, π, ln2, exp, log, sqrt | todo |
| M4 | trig, arctan, arcsin/arccos, hyperbolic, rpow, logb, sinc; complex basics (M4c); Basic.lean + M4 Compositions green | todo |
| M5 | discrete answers, finite sums; Discrete/Sums/Special(T20) | todo |
| M6 | branch & bound, box goals, roots | todo |
| M7 | AD + monotone leaves | todo |
| M8 | ranges, extrema | todo |
| M9 | Taylor models + Taylor capabilities | todo |
| M10 | quadrature, integrability; M10c complex integrals | todo |
| M11 | infinite series (AIA, tails, non-summability); M11c | todo |
| M12 | meta adaptive (convergence caps); M12c | todo |
| M13 | meta integral + piecewise polynomials | todo |

## Done

(nothing yet)

## Next

M0 → M1: vendor `LeanCert/Core/Dyadic.lean`, write `Num/Dy.lean` rounding API.

## Known gaps / risks

* Kernel speed ≈ 4000 Taylor steps/s (200-bit integers, measured
  2026-09-30 with a structural-recursion exp series).  Heavy certificates must
  go native under `auto`.
* Computability of `Fn1` records containing `Real.*` in `Prop` fields must be
  confirmed in M2 (see 03 §3).

## Deferred notes (special functions, for later phases)

* Gamma: shift `s` into `(0,1]` with `Real.Gamma_add_one`; `Real.Gamma_eq_integral`
  split at `X = 40`: `∫_0^X e^{-t}t^{s-1} = Σ (-1)^k X^{s+k}/(k!(s+k))` (termwise
  integration of the exp series, `integral_rpow`), tail `≤ X^{s-1}e^{-X}`.
* zeta (real `s > 1`): `zeta_eq_tsum_one_div_nat_add_one_cpow`, partial sums +
  integral-test tail.
* Euler γ: `eulerMascheroniSeq n < γ < eulerMascheroniSeq' n` (width ~ 1/n).
* digamma at naturals: `Complex.digamma_nat_add_one` (`H_n - γ`).
* agm: `NNReal.agmSequences_fst_le_agm`, `NNReal.agm_le_agmSequences_snd`.
* Hypergeometric (|z| < 1): coefficient lemma
  `coeff_regularizedGaussHGFunSeries`, ratio-test tails.
