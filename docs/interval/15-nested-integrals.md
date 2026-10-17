# Recursive real integration

`Goals/NestedIntegral.lean` is a fallback after the existing one-dimensional
solver. Real iterated integrals use a level-indexed syntax with a scope check.
Answer constructors and separately defined integrands use the same compiler.
An inner bound may depend on every surrounding binder; repeated binder names
are resolved by free-variable identity. Capture-avoiding level shifts also
handle bounds that themselves contain integrals. The compiler supplies equality proofs
for each operation and each integral, rather than assigning a meaning to a
parsed string.

`NestedSearch.lean` uses adaptive Gauss–Legendre/Petras quadrature. Accurate
inner quadrature runs at real quadrature nodes. Complex ellipse queries use
`NestedBounds.lean`: finite uniform bounds, normalized interval lengths, and
uniform endpoint majorants. They never run accurate complex inner quadrature.
Complex integration is not part of the public interface.

All levels share checked Legendre nodes and weights. Replay uses a small
resizing hash table with Nat indices, so its indexing reduces in the kernel. Subintegral cache keys
include a canonical expression and the exact interval environment, with unused
coordinates erased. Half-line normalization shares translation-invariant
kernels; bounds containing nested integrals retain their source identity to
preserve their convergence obligations. `NestedCert.lean` replays entries in postorder; samples
can consume only earlier results or independently computed coarse bounds.
Certificates contain instructions and domains, never trusted integral values.
The final enclosure is compared strictly against the requested rational and
tolerance using the existing interval comparison checker.

Finite oriented integrals retain endpoint uncertainty and sign. Set intervals
retain their empty-domain convention. Half-lines use `a ± t/(1-t)` with
Jacobian `(1-t)^(-2)`; the implementation evaluates the displacement as
`1/(1-t)-1` to avoid dependency loss in complex boxes. Whole-line integrals
split at zero or a visible translation center. Algebraic endpoint singularities can use power substitutions;
otherwise endpoint strips require explicit integrable power/log/decay
majorants. Exponential decay uses `exp(-s) ≤ n!/s^n`, never sample fitting.
Very small exponentials retain a positive `2^(-k)` enclosure; they are not
rounded to exact zero. This bounds dyadic exponent sizes in transformed tails.
Endpoint estimates used for a complex parameter query are uniform on the
entire parameter box.

`NExpr.Converges` requires ordinary convergence recursively on the open
integration domains. A divergent inner Bochner integral is never accepted
merely because Mathlib assigns it a default zero. Unsupported bounds or
majorants cause search/check failure. This does not establish divergence of
the literal outer Bochner integral.

The hard mathematical obligations currently contain the authorized `sorry`.
`Math/NestedDefs.lean`, `Math/NestedSubstitution.lean`, and
`Math/NestedAnalysis.lean` are mirrored in
`/tmp/intgrl`, with only small Mathlib-only dependencies. Interval-specific
bridges remain in `NestedSound.lean`. Its Gauss panel proof explicitly
composes checked nodes, inexact real sample enclosures, and
`gauss_error_real_affine`. Kernel/native/auto selection uses the existing
trust driver and a recursive cost estimate.

Regression declarations have independent finite heartbeat caps. To update a
cap, replace that declaration's `set_option maxHeartbeats … in` with Mathlib's
`#count_heartbeats in` in a temporary copy, run it using the normal Lake
environment, and set the source cap to `ceil(105*count/100)`. Counting wrappers
must not remain in committed tests, since they disable the cap. Heartbeats do
not measure native wall time. Existing one-dimensional caps are preserved.

The recursion has no fixed dimension limit, but nested quadrature can require
exponentially many samples. Search shares a finite work budget across levels.
The integration compiler currently supports elementary real kernels, not every
function in the general point-evaluation registry. Public complex paths,
unsupported special functions, arbitrary measurable domains, automatic
Fubini conversions, and arbitrary multivariate change-of-variable proofs
remain outside this implementation.

The regression files are `Test/IntervalArith/NestedIntegrals.lean` (23
integration declarations, including the four FLINT comparison problems) and
`Test/IntervalArith/NestedCertificates.lean` (five rejection groups). Numerical
witness guards are independent rational computations. Both default native
checking and an explicitly forced kernel check have axiom-footprint guards.
The current numerical targets are 10^(-5) and 10^(-6); these test runs are not
speed comparisons against FLINT's 64-bit or 128-bit benchmark targets.

Still unsupported: integration of the unimplemented erf/Si/Weierstrass and
other special-function kernels, public complex contours, general product
measure domains (including the ten-dimensional cube testcase), and improper
or singular families for which the uniform majorant classifier fails. A
supported elementary function alone does not guarantee that every domain or
composition has a suitable bound. Such cases fail without fabricating a
numerical witness.
