import Lynth.Interval.Core.Ty
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Evaluation context

Working precision plus cached enclosures of constants used by many functions.
`Ctx.Valid` records that the cached enclosures are correct; function
soundness lemmas assume it.  `Ctx.make` (in `Fns/Const.lean`) builds a valid
context with tight constants; `Ctx.coarse` is valid with trivial constants.
See `docs/interval/03-expr-registry.md §2`.
-/

namespace Lynth.Interval

structure Ctx where
  /-- working precision (mantissa bits) -/
  prec : Nat
  /-- enclosure of `π` -/
  pi : Ival
  /-- enclosure of `log 2` -/
  ln2 : Ival
deriving Repr, Inhabited

structure Ctx.Valid (c : Ctx) : Prop where
  pi_mem : Real.pi ∈ c.pi
  ln2_mem : Real.log 2 ∈ c.ln2

/-- context with trivial constant enclosures (always valid) -/
def Ctx.coarse (p : Nat) : Ctx := ⟨p, Ival.top, Ival.top⟩

theorem Ctx.coarse_valid (p : Nat) : (Ctx.coarse p).Valid :=
  ⟨Ival.mem_top _, Ival.mem_top _⟩

end Lynth.Interval
