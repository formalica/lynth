# 11 — Vendoring LeanCert (selective, Apache-2.0)

Source: `~/leancert` (LeanCert, Lean `v4.34.1`, Mathlib `v4.34.1`; Lynth is on
`v4.34.0` — expect only trivial API drifts).  License: Apache-2.0 — keep the
original copyright header and add a line
`Adapted for Lynth (namespace Lynth.Interval.Vendor); modifications: …`.
Also add `Lynth/Interval/Vendor/NOTICE.md` listing every copied file.

| LeanCert file | destination | use |
|---|---|---|
| `Core/Dyadic.lean` (1053 l.) | `Vendor/Dyadic.lean` | `Dy` core ops + proofs (02 §1) — **copy first (M1)** |
| `Core/IntervalRat/Taylor.lean` (2243 l.) | `Vendor/TaylorBounds.lean` (subset) | Taylor remainder lemmas for exp/sin/cos (`exp_taylor_remainder_in_interval`, `sin_…`, `cos_…`), atanh series (`Real.atanh_hasSum'`, `atanh_taylor_remainder_in_interval`), `mem_ln2Computable` — used as proof templates for our kernels |
| `Core/IntervalRat/Transcendental.lean` (713 l.) | `Vendor/SqrtBounds.lean` (subset) | `sqrtRatLowerPrec_le_sqrt`, `sqrt_le_sqrtRatUpperPrec` |
| `Core/TrigReduction.lean` (143 l.) | `Vendor/TrigReduction.lean` | trig argument reduction lemmas |
| `Core/LogBounds.lean` (453 l.) | as needed | log bounds |
| `Engine/CompPoly.lean` (453 l.) | `Vendor/CompPoly.lean` (M9) | computable dyadic polynomials / TMs |
| `Engine/TaylorModel/Core.lean` (1383 l.) | proof templates (M9) | TM add/mul correctness (`foil_to_trunc_remainder`, `mul_evalSet_correct`), Bernstein enclosure (`bernstein_enclosure_01`) |
| `Engine/Integrate.lean` (787 l.) | `Vendor/IntegralBounds.lean` (M10) | `integral_bounds_of_bounds`, partition additivity |
| `Engine/AD/Correctness.lean` (588 l.) | proof templates (M7) | chain rule patterns for interval AD |
| `Engine/RootFinding/Bisection.lean` | templates (M6) | bisection soundness |

Rules:
* Vendored files may keep their own `IntervalRat`-based statements; our code
  talks to them only through thin adapter lemmas in `Num/` and `Fns/`.
* Do not vendor LeanCert's `Expr`, evaluators, tactics or its function enum.
* Remove `native_decide` uses and `sorry`s (there must be none in Lynth).
* Every vendored file must build warning-free with `lake build`.
