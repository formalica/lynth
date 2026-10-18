# Internal integration proofs — 2026-10-18

The integration audit found 19 interval-specific theorem bodies with `sorry`
that have no counterpart in `/tmp/intgrl`. Sixteen now have Lean proofs in the
project: eight from the first pass and eight of the subsequent eleven.
Three internal placeholders remain. The 95 previously handed-off mathematical
obligations retain their placeholders. At the user's request, 16 further
portable mathematical obligations are now in the handoff described below.

| File | Proved theorem |
|---|---|
| `Integral/Divergence.lean` | `conditionCheck_sound` |
| `Integral/Engine.lean` | `tailEncl_transport`, `logarithmEncl_transport`, `sqrtWeightEncl_transport` |
| `Integral/Panel.lean` | `analyticBound_sound`, `gaussSamples_sound`, `errorBound_sound` |
| `Integral/Panel.lean` | `specialize_sound`, `pointPair_sound`, `onInterval_sound`, `NodeTable.sound` |
| `Integral/Cert.lean` | `finiteAssembly_sound` |
| `Integral/NestedPrimitiveProof.lean` | `safeExp_sound` (moved from `NestedSound.lean`) |
| `Integral/NestedSound.lean` | `samples_sound`, `coarsePanel_sound`, `replay_induction` |

The hybrid Legendre evaluator now has interval proofs for every numerical
branch. Supporting modules prove the exact integer coefficient recurrences,
rectangular splitting, fixed-point input quantization and transport,
polynomial differentiation, the asymptotic accumulation loop and phase
identity, negative-node parity, interval transport, symmetric root isolation,
and certified weights. The existing portable mathematical contracts supply
the Legendre identities and analytic error estimates.

Finite assembly proves partition concatenation, orientation, uncertain
endpoint contributions, and the finite endpoint conventions. Nested support
also proves environment extension, measurability with moving limits,
arithmetic evaluation, and the sample summation loop. Direct nested panels
now call `evalWith` with an empty memo and retain a finite-range check, so
their proof can reuse arithmetic evaluation and the generic integral-product
adapter. This avoids a second arithmetic correctness argument in the panel
proof. These nested proofs still depend on the unfinished evaluator contract.

Canonical memo replay now has a complete induction proof. Its supporting
modules verify half-line normalization, values and recursive convergence
under substitution, agreement at used environment slots, masked environments,
key equality, bucket lookup, insertion, resizing, and the replay loop.
Replay rejects empty parameter boxes before storing a canonical key. Without
this check, a vacuous assertion on an empty source environment could be
reused at an inhabited environment after an unused slot was erased. The
rejection regression measured 473 heartbeats and has cap 497 (+5%, rounded up).

Further completed helpers for the three remaining proofs are:

- `NestedShiftProof.lean`: inserting binder levels preserves both values and
  recursive ordinary convergence, including integrals inside endpoints.
- `NestedFormulaProof.lean`: the complete formula recognizer is sound,
  including its nonnegative guards, exponential tails, logarithms, both
  endpoint power kernels, and finite endpoint conventions.
- `NestedPrimitiveProof.lean`: real-value correctness of every successful
  complex fallback primitive, binary operation, and power routine. This
  accounts for the real branch choices for logarithm, square root, absolute
  value, and floor; it does not yet prove the analytic extension contract.
- `NestedEndpointProof.lean`: the numerical moment-sum loop and coefficient
  radius give the claimed endpoint remainder. Given a valid scaled envelope,
  the existing portable remainder theorem establishes integrability and the
  numerical error bound.
- `NestedScaleProof.lean`: exact scaled-envelope arithmetic for constants,
  the endpoint variable, negation, addition, subtraction, multiplication,
  division, natural powers, power/logarithm rescaling factors, and `collapse`.
- `NestedScaledRealProof.lean`: the real coefficient of a scaled enclosure,
  rational powers, and every branch of scaled unary evaluation, including
  logarithmic growth and exponential decay.

These helper modules contain no placeholders. The recursive `scaled`
evaluator still needs its induction, particularly the nested-integral cases,
connected to these operation proofs. The completed endpoint adapter alone is
not a proof of the full recursive range evaluator or assembly theorem.

## Portable mathematical handoff

`Math/NestedEnvelope.lean` has 12 obligations and imports only Mathlib. They
cover power/log absorption, real and complex scaled logarithms, exponential
decay, rational powers, complex integral means, affine substitution, remainder
estimates, truncation assembly, and holomorphic parameter integrals in general
normed complex parameter spaces. Four are already used by the `collapse` and
scaled real unary/power proofs. The other eight support the remaining work.

`Math/NestedChange.lean` has four obligations: scope preservation of formulas
and transformations, scope/purity of the split anchor, and transport of both
ordinary recursive convergence and values through changes of variables.
Its pure definitions now live in `Math/NestedSyntax.lean`. Those definitions
were moved unchanged from `NestedExpr.lean` and `NestedBounds.lean`; numerical
evaluation and memo tables remain in their original implementation modules.
`center_properties` is already used by the split assembly proof.

Copies and their mathematical support files are in `/tmp/intgrl`. Every file
was compiled from that directory using imports of Mathlib and the local
support modules; no Lynth import is present in the handoff. See
`/tmp/intgrl/README.md` for the theorem list, dependency order and return format.
These 16 obligations deliberately retain `sorry` in the project and handoff.

Whole-line split assembly is now proved, including convergence at the common
endpoint of the open half-lines. Both `entryEncl` and the independent `boundC`
fallback check the integrand at that point before combining half-line results. For example,
`x^2*exp(-x^2)*integral_0^1 1/(x^2+y^2) dy` has a divergent inner integral at
`x=0` even though the outer factor vanishes and the two open half-lines
converge. A regression checks rejection of the split when its half-line
results have been preloaded. It measured 454 heartbeats and has cap 477 (+5%).

| File | Remaining theorem | Unfinished work |
|---|---|---|
| `Integral/NestedSound.lean` | `evalWith_sound` | Connect the independent recursive integral range evaluator (`boundR` and its complex fallback) to the completed arithmetic/formula/scaled-unary helpers and finish scaled integral envelopes. Arithmetic and memo-hit branches are proved. |
| `Integral/NestedSound.lean` | `analytic_sound` | Analytic extensions and uniform complex bounds for recursive integrals. |
| `Integral/NestedSound.lean` | `assembly_sound` | The split branch uses `splitEntry_sound`. The remaining hole covers panel partitions, endpoint majorants, and substitutions. |

A binder bug was found while inspecting the recursive range proof. The
power-integral recognizer compared an outer endpoint directly with a copy
inside the integrand. If the endpoint contained an integral, its own binder
needed to move past the outer integration binder. The recognizer now shifts
such endpoints before matching. For example, let
`a = integral 0..(1/100) (var 0)` and consider the scoped raw expression
`integral a..1 ((var 0 - a)^1)`, with the same unshifted syntax for `a` in
the body. Its actual value is `39599999901/80000000000` (about `0.495`), but
the old shortcut returned an interval near `0.5` that excluded it. The new
certificate regression rejects that formula match, accepts the correctly
shifted version, and checks enclosure of the actual value. It used
665 heartbeats with `#count_heartbeats`; its individual cap is 699 (+5%,
rounded up). Existing test caps were not increased.

The apparent `emIntegral_eq` placeholder in `Fns/ZetaEM.lean` is inside a
comment describing a rejected statement; its corrected live theorem is proved.
This audit concerns integration and its special functions and excludes older
placeholders in unrelated hypergeometric/grind modules.

Axiom inspection confirms that the coefficient generators, rectangular
splitting, input quantization, and empty-memo validity have no `sorryAx`
dependency. The new binder insertion, power-kernel recognition, complex
squaring/natural powers and binary operations, numerical endpoint moment
loop, and scaled arithmetic proofs also have no `sorryAx` dependency. Formula
dispatch, unary branch agreement and endpoint integration inherit the existing
portable mathematical contracts. The completed adapters still inherit portable mathematical
contracts, and the nested adapters additionally inherit unfinished internal
contracts. This work does not remove `sorryAx` from final integral proofs.

Validation: `lake build Test.IntervalArith` completed successfully with
18,598 jobs, including the new split-point regression. All existing per-test
heartbeat caps were retained. The nine handoff modules also compiled with the
Lynth library directory removed from `LEAN_PATH`; the mathematical packet is
independent of the implementation library.

Earlier build and axiom-audit logs are saved under
`/tmp/lynth-remaining-proofs/`; the new portable-lemma work and standalone
checks are logged under `/tmp/lynth-portable-nested/`. The regression source records the historical
counterexample and the measured heartbeat budgets. No mathematical packet
previously handed off in `/tmp/intgrl` was modified or proved in this pass.
