-- Translation from Lean `Int`/`Nat` comparisons to `Fourier.LeC` systems.
--
-- This is the arithmetic procedure's internal theory boundary (à la Z3
-- theory solvers with their own language): linear terms become
-- coefficient vectors over an atom table, comparisons become `≤`
-- constraints. Nonlinear subterms (`x * y`, `a - b` on `Nat`, divisions)
-- become opaque atoms — sound for refutation, since every occurrence maps
-- to the same atom. `Nat` comparisons map through `Int` exactly for
-- `≤`/`<`/`=`; `Nat` subtraction truncates, so it is kept opaque.
import Lean
import Lynth.Arith.Linear
import Lynth.Arith.Fourier

namespace Lynth.Arith.Recognize

open Lean Elab Tactic Meta

/-- A linear term: `∑ coeffs[i]·atomᵢ + const`. -/
structure LinTerm where
  coeffs : Array Rat
  const : Rat

/-- Pad to length `n`. -/
def padTo (n : Nat) (a : Array Rat) : Array Rat :=
  a ++ Array.replicate (n - a.size) 0

/-- Term addition / subtraction / scaling. -/
def addT (x y : LinTerm) : LinTerm :=
  let n := Nat.max x.coeffs.size y.coeffs.size
  { coeffs := Array.zipWith (· + ·) (padTo n x.coeffs) (padTo n y.coeffs),
    const := x.const + y.const }

def negT (x : LinTerm) : LinTerm :=
  { coeffs := x.coeffs.map (· * -1), const := -x.const }

def subT (x y : LinTerm) : LinTerm :=
  addT x (negT y)

def scaleT (k : Rat) (x : LinTerm) : LinTerm :=
  { coeffs := x.coeffs.map (· * k), const := x.const * k }

def constT (k : Rat) : LinTerm :=
  { coeffs := #[], const := k }

/-- Strip `Int.ofNat` / `Nat.cast` wrappers (atoms are shared across the
`Nat`/`Int` boundary by underlying integer value). Fuel-bounded. -/
def stripCast : Expr → Nat → Expr
  | e, 0 => e
  | e, fuel + 1 =>
    match e.getAppFn with
    | .const n _ =>
      if n == ``Int.ofNat then
        let args := e.getAppArgs
        if args.size == 1 then stripCast args[0]! fuel else e
      else if n == ``Nat.cast then
        let args := e.getAppArgs
        if args.size == 3 then stripCast args[2]! fuel else e
      else e
    | _ => e

/-- Numeric literal evaluation (after `whnfR` + cast stripping). -/
def asNumeral (e : Expr) : Option Rat :=
  match e with
  | .lit (.natVal n) => some (n : Rat)
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
    some (n : Rat)
  | .app (.const ``Int.negSucc _) (.lit (.natVal n)) =>
    some (-((n : Rat) + 1))
  | _ => none

/-- Binary head-operator split: `(headName, lhs, rhs)` from last two args. -/
def asBinOp (e : Expr) : Option (Name × Expr × Expr) := do
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if args.size < 2 then none
    else some (n, args[args.size - 2]!, args[args.size - 1]!)
  | _ => none

/-- Unary head-operator split. -/
def asUnOp (e : Expr) : Option (Name × Expr) := do
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if args.size < 1 then none
    else some (n, args[args.size - 1]!)
  | _ => none

/-- Constant evaluation for scalar sides (`k * t`): numerals and negated
numerals. -/
def constNum (e : Expr) : MetaM (Option Rat) := do
  let e ← whnfR e
  let e := stripCast e 8
  match asNumeral e with
  | some k => pure (some k)
  | none =>
    match asUnOp e with
    | some (n, a) =>
      if n == ``Neg.neg then
        match asNumeral (stripCast (← whnfR a) 8) with
        | some k => pure (some (-k))
        | none => pure none
      else pure none
    | none => pure none

/-- Allocate (or look up) the atom id for `e`. -/
def atomId (atoms : IO.Ref (Array Expr)) (e : Expr) : MetaM Nat := do
  let arr ← atoms.get
  match arr.findIdx? (· == e) with
  | some i => pure i
  | none => atoms.set (arr.push e); pure arr.size

/-- Opaque atom term for `e`. -/
def atomT (atoms : IO.Ref (Array Expr)) (e : Expr) : MetaM LinTerm := do
  let i ← atomId atoms e
  pure { coeffs := Array.replicate (i + 1) 0 |>.set! i 1, const := 0 }

/-- Recognize a linear term. `natMode = true` means the enclosing
comparison is over `Nat` (so `HSub` truncates and stays opaque). -/
partial def recognize (atoms : IO.Ref (Array Expr)) (e : Expr)
    (natMode : Bool) : MetaM LinTerm := do
  let e := stripCast (← whnfR e) 8
  if let some k := asNumeral e then return constT k
  if let some (n, a, b) := asBinOp e then
    if n == ``HAdd.hAdd then
      return addT (← recognize atoms a natMode) (← recognize atoms b natMode)
    else if n == ``HSub.hSub then
      if natMode then return (← atomT atoms e)
      else
        return subT (← recognize atoms a natMode) (← recognize atoms b natMode)
    else if n == ``HMul.hMul then
      match (← constNum a), (← constNum b) with
      | (some x), (some y) => return constT (x * y)
      | (some x), none => return scaleT x (← recognize atoms b natMode)
      | none, (some y) => return scaleT y (← recognize atoms a natMode)
      | none, none => return (← atomT atoms e)
    else return (← atomT atoms e)
  else if let some (n, a) := asUnOp e then
    if n == ``Neg.neg then
      return negT (← recognize atoms a natMode)
    else if n == ``Nat.succ then
      -- `Nat.succ a = a + 1`
      let ta ← recognize atoms a natMode
      return addT ta (constT 1)
    else return (← atomT atoms e)
  else return (← atomT atoms e)

/-- Split `e` as `(comparison, lhs, rhs)` for `LE.le`/`LT.lt`/`Eq`. -/
def asComp (e : Expr) : MetaM (Option (Cmp × Expr × Expr)) := do
  let e ← whnfR e
  match e.getAppFn with
  | .const n _ =>
    let args := e.getAppArgs
    if args.size < 2 then return none
    let a := args[args.size - 2]!
    let b := args[args.size - 1]!
    if n == ``LE.le then return some (.le, a, b)
    else if n == ``LT.lt then return some (.lt, a, b)
    else if n == ``Eq then return some (.eq, a, b)
    else return none
  | _ => return none

/-- Check the comparison is over `Int` (`false`) or `Nat` (`true`). -/
def intOrNatMode (e : Expr) : MetaM (Option Bool) := do
  let t ← whnfR (← inferType e)
  if t.isConstOf ``Int then pure (some false)
  else if t.isConstOf ``Nat then pure (some true)
  else pure none

/-- Hypothesis comparison to `≤`-terms. Over the integer fragment these
are exact: `t < 0` ⟺ `t + 1 ≤ 0`; `=` splits. -/
def hypTerms (atoms : IO.Ref (Array Expr)) (k : Cmp) (a b : Expr)
    (natMode : Bool) : MetaM (List LinTerm) := do
  let ta ← recognize atoms a natMode
  let tb ← recognize atoms b natMode
  let t := subT ta tb
  match k with
  | .le => pure [t]
  | .lt => pure [addT t (constT 1)]
  | .eq => pure [t, negT t]

/-- Negated-goal comparison to `≤`-terms, exact over integers:
`¬(t ≤ 0)` ⟺ `-t + 1 ≤ 0`; `¬(t < 0)` ⟺ `-t ≤ 0`.
`Eq` goals are left to other procedures. -/
def negTerms (atoms : IO.Ref (Array Expr)) (k : Cmp) (a b : Expr)
    (natMode : Bool) : MetaM (Option (List LinTerm)) := do
  let ta ← recognize atoms a natMode
  let tb ← recognize atoms b natMode
  let t := subT ta tb
  match k with
  | .le => pure (some [addT (negT t) (constT 1)])
  | .lt => pure (some [negT t])
  | .eq => pure none

/-- Build the `≤` system from `Prop` hypotheses plus the negated goal.
`none` ⟹ goal shape unsupported (other procedures take over). -/
def buildSys : TacticM (Option (List Fourier.LeC)) := do
  let atoms ← IO.mkRef #[]
  let mut raw : Array LinTerm := #[]
  for decl in ← getLCtx do
    -- skip auxiliary decls (e.g. Lean's `_example` self-reference)
    if (decl.kind == .default) && (← isProp decl.type) then
      if let some (k, a, b) := ← asComp decl.type then
        if let some natMode := ← intOrNatMode a then
          raw := raw ++ (← hypTerms atoms k a b natMode).toArray
  let goal ← getMainTarget
  match ← asComp goal with
  | none => return none
  | some (k, a, b) =>
    match ← intOrNatMode a with
    | none => return none
    | some natMode =>
      match ← negTerms atoms k a b natMode with
      | none => return none
      | some ts => raw := raw ++ ts.toArray
  if raw.isEmpty then return none
  -- Explosion guard: FM can double constraints per eliminated variable;
  -- oversized systems skip the oracle (`omega` still tries downstream).
  if 48 < raw.size then return none
  let nVars := raw.foldl (fun m t => Nat.max m t.coeffs.size) 0
  let nOrig := raw.size
  let sys := raw.toList.zipIdx.map fun (t, k) =>
    let coeffs := (padTo nVars t.coeffs).toList
    Fourier.mkLe coeffs t.const nOrig k
  pure (some sys)

end Lynth.Arith.Recognize
