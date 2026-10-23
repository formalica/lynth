module

import Lynth
public meta import Lean.Util.CollectAxioms

/-! Consumer checks use the ordinary facade, without implementation imports. -/

#check_failure Lynth.Frontend.dispatch
#check_failure Lynth.Interval.Procedure.run
#check_failure Lynth.Interval.Ival.mem_add
#check_failure Lynth.Interval.Fns.mem_monoNIval
#check_failure Lynth.Interval.Ty.asyHolds_top
#check_failure Lynth.Interval.CheckReduction.derive
#check_failure Lynth.Interval.kernelEvidence

set_option lynth.interval.trust "kernel" in
private theorem kernelPoint : Real.sqrt 2 < (3 : ℝ) / 2 := by lynth

set_option lynth.interval.trust "kernel" in
private theorem kernelComplex : (Complex.exp (1 : ℂ)).re < 3 := by lynth

set_option lynth.interval.trust "kernel" in
private theorem kernelIntegral : (∫ x in (0 : ℝ)..1, x ^ 2) < 1 := by lynth

-- Independent certificates use the same shared compatibility theorems.
set_option lynth.interval.trust "kernel" in
private theorem kernelIntegralAgain : (∫ x in (0 : ℝ)..1, x ^ 2) < 2 := by lynth

set_option lynth.interval.trust "kernel" in
private theorem kernelNestedIntegral :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..x, y) < 1 := by lynth

set_option lynth.interval.trust "kernel" in
private def kernelQuadrature :
    {q : ℚ // |(∫ x in (0 : ℝ)..1, Real.exp (-x ^ 2)) - (q : ℝ)| < 1 / 100} := by
  lynth

set_option lynth.interval.trust "native" in
private theorem nativeIntegral : (∫ x in (0 : ℝ)..1, x ^ 2) < 1 := by lynth

run_meta do
  unless (← Lean.getEnv).header.importAllModules.isEmpty do
    throwError "Ordinary Lynth imports must not enable private-module name searches"
  let standard := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``kernelPoint, ``kernelComplex, ``kernelIntegral, ``kernelIntegralAgain,
      ``kernelNestedIntegral, ``kernelQuadrature] do
    let axioms ← Lean.collectAxioms name
    let unexpected := axioms.filter fun ax => !standard.contains ax
    unless unexpected.isEmpty do
      throwError "Unexpected axioms in {name}: {unexpected}"
  -- The generic Array/Range proofs belong to the library theorem bodies.
  -- Certificates from independent goals must apply the same shared theorem.
  let sharedLemmas := [
    (``Lynth.Interval.Integral.integralCheck, ``Lynth.Interval.CheckReduction.integralCheck),
    (``Lynth.Interval.Integral.Nested.check, ``Lynth.Interval.CheckReduction.nestedCheck),
    (``Lynth.Interval.Composition.integralCheck, ``Lynth.Interval.CheckReduction.compositionCheck),
    (``Lynth.Interval.Integral.divergenceCheck, ``Lynth.Interval.CheckReduction.divergenceCheck)]
  let mut sharedCertificates : Nat := 0
  for ci in (← (← Lean.getEnv).getLocalConstantInfos) do
    let .thmInfo info := ci.toConstantInfo | continue
    unless info.name.toString.contains "lynth_interval_cert" do continue
    let some (_, lhs, _) := info.type.eq? | continue
    for (checker, theoremName) in sharedLemmas do
      unless lhs.isAppOf checker do continue
      unless info.value.getAppFn.isConstOf theoremName do
        throwError "Certificate {info.name} did not use the shared kernel lemma"
      sharedCertificates := sharedCertificates + 1
  unless sharedCertificates ≥ 4 do
    throwError "Expected independent certificates using the shared kernel lemmas"
