module

public import Lynth.Basic
public import Lynth.ProofInterface
public import Lynth.Options
public import Lynth.ComplexFuncs
public import Lynth.Hypergeometric.Defs
public import Lynth.Analysis.SpecialFunctionsDefs
public import Lynth.Analysis.RealFunctions
public import Lynth.Analysis.ClassicalFunctions

import Lynth.Certificates
import Lynth.Frontend
import Lynth.HyperGeomIdentities

/-! The public entry point for `lynth`, its options, mathematical functions, and
the declarations needed to check generated proofs.
The selected internal helpers exercised by unit tests are also exported here.
The separate `lynth_grind` API uses `Lynth.Grind.Tactic`.
-/
