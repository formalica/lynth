# Lynth interval arithmetic — implementation spec (index)

This directory is the **binding implementation spec** for the interval
arithmetic (IA) procedure of `lynth`: rigorous, proof-producing numerics over
`ℝ` and `ℂ` (point values, finite/infinite sums, integrals, box inequalities,
ranges, roots, extrema, and *meta* goals that synthesize computable
approximation functions).  It is written so that any agent/session can pick up
the work: read this file, then `13-progress.md`, then the file of the phase
you are working on.

| File | Content |
|---|---|
| `01-architecture.md` | layers, data flow, module layout, dispatch integration, trust modes, config |
| `02-numerics.md` | dyadic numbers, rounding, extended real intervals, ℕ-intervals, complex boxes, proof obligations |
| `03-expr-registry.md` | typed AST, function records + capabilities, denotation, evaluator, soundness, registry attribute, reifier, exact evaluator, **how to add a function** |
| `04-functions.md` | per-function algorithms and Mathlib lemma sources (real + complex) |
| `05-point-goals.md` | Phases 1–3: point approximations, closed inequalities, floor/ceil/sign, finite sums, certificates |
| `06-box-goals.md` | Phase 4: branch & bound, AD, ranges, roots, extrema |
| `07-integrals.md` | Phase 5: Taylor models, quadrature, integrability |
| `08-series.md` | Phase 6: infinite sums, summability, tails, non-summability |
| `09-meta.md` | Phase 7: meta goals (adaptive precision + piecewise polynomials) |
| `10-complex.md` | complex boxes and complex functions across **all** phases |
| `11-vendoring.md` | which LeanCert files are copied/adapted and how |
| `12-tests.md` | test inventory, per-test route, test fixes, new complex tests |
| `13-progress.md` | living status: milestones, done/next, known gaps |

## Decisions log (binding; from the user, 2026-09-30)

1. **Trust**: implement *both* modes, selected by a `lynth` config parameter:
   `kernel` (all certificates checked by kernel reduction, `decide +kernel`
   style — axioms stay `[propext, Classical.choice, Quot.sound]`) and
   `native` (certificates checked by `native_decide`; in Lean 4.34 this adds a
   per-declaration auxiliary axiom `…._native.native_decide.ax_…`), plus
   `auto` = kernel when the static cost estimate is below budget, native
   otherwise.  See `01-architecture.md §Trust`.
2. **Tests**: broken test *statements* may be fixed minimally (list in
   `12-tests.md`); MP31 moves to a convergent point `|z| < 1`.
3. **Meta goals**: adaptive precision evaluation (`Nat.find` over precision,
   justified by per-function convergence lemmas) is the default; piecewise
   polynomial approximations are used when the input range is bounded and the
   function is tame.
4. **Scope**: phases 1–7 in full; of the former phases 8/9 only **complex
   boxes** — complex support is required in *all* goal kinds.  Special
   functions (Gamma, zeta, γ, digamma, agm, hypergeometric), `deriv`, Taylor
   coefficients, ODEs, linear algebra, improper integrals and divergence proofs
   are deferred (listed in `12-tests.md` as "deferred").
5. **Time budget**: ≤ 60 s elaboration + checking per declaration.
6. **LeanCert** (`~/leancert`, Apache-2.0): selective vendoring into
   `Lynth/Interval/Vendor/` (keep license headers).  Not the whole tree.
7. Local git commits at milestones are allowed; no pushes.

## Non-negotiable principles

* **One open function registry.**  No closed enum of functions.  Adding a
  function = one new file with one `Fn*` record + `@[lynth_fn]` attribute; the
  core (evaluator, soundness, reifier, goal handlers) is never edited.
* **Soundness is proved once, generically** by induction over the AST, using
  the per-function `sound` field.  Per-function obligations are local.
* **Search is untrusted and native** (precompiled Lynth code at elaboration
  time); **checking is a single reflective Bool computation** whose soundness
  theorem yields the user goal.
* **No `sorry`, no new `axiom`** in `Lynth/` (repository rule).  Temporary
  gaps must be explicit `yield`s of the procedure, never fake proofs.
* Every goal handler *yields* (returns `.failure []`, goal untouched) on shapes
  it does not recognize, so later procedures still run.
* Complex numbers are first-class: every generic component is parameterized by
  the value type `Ty` (`real | cplx | nat`).
