# 20 — Composing real integrals and sums

`Lynth/Interval/Composition/Bounds.lean` and `Eval.lean` add a recursive real
enclosure handler after the existing specialized goal handlers. Each evaluated
subexpression supplies its source term, an interval, and a membership proof.
The ordinary expression evaluator then combines those intervals using the
registered functions' soundness rules. Integral and sum values can therefore
occur inside arithmetic, including expressions such as
`2 * ((∫ x in 0..1, f x) - q) * Real.exp 1`.

## Binders and parameters

Finite sums over a closed `Finset.range n` are expanded with proved equalities
before evaluation, using a balanced addition tree for long prefixes. Lean's
binder substitution handles shadowed variables and index-dependent integration
endpoints. Expansion currently limits `n` to 4096.
User definitions are unfolded when ordinary reification cannot handle them.

Local real variables can be enclosed using rational lower and upper bounds
from the context, including `x ∈ Set.Icc a b`. The same boxes accompany an
integrand or summand while its own binder varies. The handler introduces
universal binders and bounded hypotheses before proving numerical comparisons.

## Infinite sums

`ParametricSeries.asy` uses the existing open function registry's asymptotic
capabilities, retaining the boxes of real parameters. A successful tail check
proves summability and bounds every remaining term, in addition to evaluating
the finite prefix. Precision follows the existing precision schedule and
certificate trust option.

For integrals inside summands, a uniform geometric or power bound on the
integrand is multiplied by a bound on the integration interval's length.
Arithmetic around those integrals composes the existing asymptotic operations.
Integration endpoints may depend on the summation index when their tails have
a certified uniform bound.

For a sum inside an integral, the handler bounds the infinite remainder
uniformly over the integration domain. It integrates the finite prefix with
the existing Gauss backend, then widens its result by the remainder bound
times the domain length. The proof also establishes interval integrability.
Linearity handles addition, subtraction, and constant scaling around such
integrands. A measurable interval-panel enclosure provides a general finite
integration fallback for other compositions.

## Scope and failure

This handler operates on real expressions. Existing complex handlers retain
their separate capabilities. Infinite sums require a tail model that the
available asymptotic rules can certify; arbitrary convergent series are not
automatically solvable. Improper integrals use the existing nested integration
backend, while the new uniform truncation and integral tail rules require
bounded finite integration domains. Interval dependency and panel limits can
prevent a requested tolerance from being reached.

Unsupported cases yield without changing the goal. The new lemmas contain
no `sorry` or explicit axioms. Certificate checking uses the existing trust
setting, including native checking when selected. Reusing integration
certificates retains the existing integration proof dependencies described in
[18](18-internal-integration-proofs.md).

## Tests

`Test/IntervalArith/IntegralInExpression.lean` checks arithmetic around
integrals and sums, both nesting orders, infinite tails depending on an
integration variable, arithmetic inside infinite summands, dependent endpoints,
shadowed binders, local real bounds, user aliases, higher precision, and kernel
certificate mode. It also checks that a divergent constant series is rejected.
