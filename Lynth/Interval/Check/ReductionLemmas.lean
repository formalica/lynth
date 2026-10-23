module

public import Lynth.Interval.Integral.Engine
public import Lynth.Interval.Integral.Divergence
public import Lynth.Interval.Integral.NestedCert
public import Lynth.Interval.Composition.Bounds
public import Lynth.Interval.Fns.Special.Eta
public import Init.Data.Array.Lemmas
public import Init.Data.List.ToArray
public import Init.Data.Range.Lemmas
meta import all Lynth.Interval.Check.BuildReduction

/-!
Shared kernel-checking lemmas for operations whose bodies are hidden by modules.

Each integration lemma has the form
`∀ inputs, reducible_check inputs = true → original_check inputs = true`.
The reducible expression is local to the theorem statement; it is not another
executable checker. All equivalence proofs are checked while building this file
and stay inside the theorem bodies. Numerical definitions remain unchanged.

The eta lemmas also accept the Boolean context containing the function record.
Only these six theorem headers are exported; the proof automation is private.
-/

run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Integral.integralCheck `Lynth.Interval.CheckReduction.integralCheck
run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Integral.Nested.check `Lynth.Interval.CheckReduction.nestedCheck
run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Composition.integralCheck `Lynth.Interval.CheckReduction.compositionCheck
run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Integral.divergenceCheck `Lynth.Interval.CheckReduction.divergenceCheck
run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Fns.etaR `Lynth.Interval.CheckReduction.etaR true
run_meta
  Lynth.Interval.CheckReduction.derive
    ``Lynth.Interval.Fns.etaC `Lynth.Interval.CheckReduction.etaC true
