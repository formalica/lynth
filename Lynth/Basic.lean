import Lynth.Frontend

/-!
`lynth` tactic entry point.
-/
namespace Lynth

open Lean Elab Tactic

/-- Main tactic: `by lynth`. Dispatches to the procedure pipeline. -/
elab "lynth" : tactic =>
  Lynth.Frontend.dispatch

end Lynth
