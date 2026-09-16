-- Abstraction of Lean goals to `Lynth.Sat.Encode.PropForm` skeletons.
--
-- Non-propositional subterms (arithmetic, binders, opaque predicates)
-- become atoms; this is sound for validity-guided oracle use because the
-- final proof is always rebuilt by kernel-checked tactics. Hypotheses are
-- *not* abstracted yet — the oracle sees the goal only (context
-- abstraction is TODO in `docs/Z3-NOTES.md` step 1).
import Lean
import Lynth.Sat.Encode

namespace Lynth.Sat.Abstract

open Lean Elab Tactic Meta

/-- Atom table: Lean exprs assigned consecutive ids. -/
abbrev AtomTable := Array Expr

/-- Find an atom's id or allocate a fresh one (syntactic `==`). -/
def atomId (tbl : IO.Ref AtomTable) (e : Expr) : MetaM Nat := do
  let arr ← tbl.get
  match arr.findIdx? (· == e) with
  | some i => pure i
  | none =>
    tbl.set (arr.push e)
    pure arr.size

/-- Abstract `e` to a skeleton. Recognizes `True`/`False`/`And`/`Or`/
`Not`/nondependent `→`; everything else is an atom. -/
partial def abstract (tbl : IO.Ref AtomTable) (e : Expr) : MetaM Encode.PropForm := do
  let e ← whnfR e
  match e with
  | .const ``True _ => pure .tru
  | .const ``False _ => pure .fls
  | .app (.app (.const ``And _) a) b =>
    pure (.conj (← abstract tbl a) (← abstract tbl b))
  | .app (.app (.const ``Or _) a) b =>
    pure (.disj (← abstract tbl a) (← abstract tbl b))
  | .app (.const ``Not _) a => pure (.neg (← abstract tbl a))
  | .app (.app (.const ``Iff _) a) b =>
    let a' ← abstract tbl a
    let b' ← abstract tbl b
    pure (.conj (.imp a' b') (.imp b' a'))
  | .forallE _ d b _ =>
    if b.hasLooseBVars then
      pure (.atom (← atomId tbl e))
    else
      pure (.imp (← abstract tbl d) (← abstract tbl b))
  | _ => pure (.atom (← atomId tbl e))

/-- Abstract the current main goal. Returns the skeleton + atom count. -/
def abstractGoal : TacticM (Encode.PropForm × Nat) := do
  let tbl ← IO.mkRef #[]
  let goal ← getMainTarget
  let f ← abstract tbl goal
  pure (f, (← tbl.get).size)

end Lynth.Sat.Abstract
