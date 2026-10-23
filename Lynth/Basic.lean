module

public meta import Lean.Elab.Tactic.Basic
public meta import Mathlib.Tactic.Linarith
public meta import Mathlib.Tactic.NormNum
public meta import Mathlib.Tactic.Ring
public meta import Lynth.Frontend
import all Lynth.Frontend

/-!
`lynth` tactic entry point.
-/
namespace Lynth

open Lean Elab Tactic

/-- Main tactic: `by lynth`. Dispatches to the procedure pipeline. -/
elab "lynth" : tactic =>
  Lynth.Frontend.dispatch

end Lynth
