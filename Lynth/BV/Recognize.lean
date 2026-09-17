import Lean
import Lynth.BV.Blast

/-!
Translation from Lean `BitVec` terms to `BvTerm` reified terms.

Recognizes `BitVec w`-typed comparisons and terms built from
`&&&`/`|||`/`^^^`/`~~~`/`+` (both `H*` instances and direct `BitVec`
constants) plus `OfNat` literals. Anything else of `BitVec` type
becomes an opaque atom. Widths come from types and must agree;
`none` anywhere means "not a BV goal" and the procedure yields.
-/
namespace Lynth.BV.Recognize

open Lean Meta
open Lynth.BV

/-- Width of a `BitVec w` type; `none` otherwise (or non-literal `w`). -/
def asBvWidth (ty : Expr) : MetaM (Option Nat) := do
  let ty ← whnfR ty
  match ty with
  | .app (.const ``BitVec _) w =>
    let w ← whnfR w
    match w with
    | .lit (.natVal n) => pure (some n)
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
      pure (some n)
    | _ => pure none
  | _ => pure none

/-- Numeric literal value. -/
def asNumeral (e : Expr) : Option Nat :=
  match e with
  | .lit (.natVal n) => some n
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    some n
  | _ => none

/-- Allocate (or look up) the atom id for `e`. -/
def atomId (atoms : IO.Ref (Array Expr)) (e : Expr) : MetaM Nat := do
  let arr ← atoms.get
  match arr.findIdx? (· == e) with
  | some i => pure i
  | none => atoms.set (arr.push e); pure arr.size

/-- Recognize a `BitVec`-typed term at expected width `w`.
Dispatches on head name first: unary operators also satisfy the
binary arity test, so they must be checked before it. -/
partial def recognize (atoms : IO.Ref (Array Expr)) (e : Expr)
    (w : Nat) : MetaM (Option BvTerm) := do
  let e ← whnfR e
  if let some k := asNumeral e then
    return some (.const w k)
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if (n == ``Complement.complement || n == ``BitVec.not) && 1 ≤ args.size then
      match ← recognize atoms args[args.size - 1]! w with
      | some ta => return some (.not ta)
      | none => return none
    else if args.size < 2 then
      atomFallback atoms e w
    else
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      if n == ``HAnd.hAnd || n == ``BitVec.and then
        match (← recognize atoms a w), (← recognize atoms b w) with
        | some ta, some tb => return some (.and ta tb)
        | _, _ => return none
      else if n == ``HOr.hOr || n == ``BitVec.or then
        match (← recognize atoms a w), (← recognize atoms b w) with
        | some ta, some tb => return some (.or ta tb)
        | _, _ => return none
      else if n == ``HXor.hXor || n == ``BitVec.xor then
        match (← recognize atoms a w), (← recognize atoms b w) with
        | some ta, some tb => return some (.xor ta tb)
        | _, _ => return none
      else if n == ``HAdd.hAdd || n == ``BitVec.add then
        match (← recognize atoms a w), (← recognize atoms b w) with
        | some ta, some tb => return some (.add ta tb)
        | _, _ => return none
      else atomFallback atoms e w
  | _ => atomFallback atoms e w
where
  /-- Opaque atom for other heads (must be `BitVec`-typed). -/
  atomFallback (atoms : IO.Ref (Array Expr)) (e : Expr) (w : Nat) :
      MetaM (Option BvTerm) := do
    match ← asBvWidth (← inferType e) with
    | some w' =>
      if w' == w then
        let i ← atomId atoms e
        pure (some (.var w i))
      else pure none
    | none => pure none

/-- Split a goal into `(isEq, t1, t2)` for `BitVec` `=`/`≠`. -/
def asBvGoal (goal : Expr) : MetaM (Option (Bool × BvTerm × BvTerm)) := do
  let g ← whnfR goal
  let (isEq, a, b) ←
    match g with
    | .app (.app (.app (.const ``Eq _) _) x) y => pure (true, x, y)
    | .app (.app (.const ``Ne _) x) y => pure (false, x, y)
    | .app (.const ``Not _) e =>
      let e ← whnfR e
      match e with
      | .app (.app (.app (.const ``Eq _) _) x) y => pure (false, x, y)
      | _ => return none
    | _ => return none
  let wa ← asBvWidth (← inferType a)
  let wb ← asBvWidth (← inferType b)
  match wa, wb with
  | some w1, some w2 =>
    if w1 != w2 then return none
    else
      let atoms ← IO.mkRef #[]
      match (← recognize atoms a w1), (← recognize atoms b w1) with
      | some t1, some t2 => pure (some (isEq, t1, t2))
      | _, _ => pure none
  | _, _ => pure none

end Lynth.BV.Recognize
