import Lean
import Lynth.Procedure
import Lynth.Witness
import Lynth.Euf.Procedure
import Lynth.FinSearch.Detect
import Lynth.FinSearch.Recognize
import Lynth.FinSearch.Procedure

/-!
List-bound inference for synthesis over `List Nat` goals
(`{ l : List Nat // P l }`).

The `FinSearch` core only handles finite domains, so an unbounded
list goal needs its length and element values inferred first. Every
inference below is asked of every recognized call through one
dispatcher (`inferenceRow`): length lower/upper bounds for
`List`-valued calls, element lower/upper bounds and value pools for
`Nat`-element lists, target exact/lower/upper bounds answering
what a call equated to a closed value forces upon a mentioned
target list, relation lower/upper/pool/domain answers for non-`Eq`
propositions (`Sublist`/`Perm` reference domains), and peel lengths
letting equations recurse through one nesting layer at a time.
Each Lean function the pipeline handles owns exactly
one table row; unknown heads answer `none` everywhere, so shared
code never names a single function and supporting a new function
means adding a row. Recursive questions go through the `Queries`
bundle (fuel-guarded, always on strict subterms). Closed sides see
through definitions. Enumeration follows the inferred shape
(sublists of a reference, sorted-first plus bounded pool products
over a length window, widened-pool retry). A wrong inference
can only make the search miss (yield), never prove a falsehood:
every candidate is kernel-checked by `decide` before it closes
anything.
-/
namespace Lynth.FinSearch.ListInfer

open Lean Elab Tactic Meta
open Lynth.FinSearch

/-- Recursive query bundle: the uniform questions, asked of any
subterm with fuel. Rows receive it explicitly so no mutual block
is needed. -/
structure Queries where
  lenLo : Expr → Nat → MetaM (Option Nat)
  lenHi : Expr → Nat → MetaM (Option Nat)
  elemLo : Expr → Nat → MetaM (Option Nat)
  elemHi : Expr → Nat → MetaM (Option Nat)
  pool : Expr → Nat → MetaM (Option (List Nat))

/-- Reference domain governing the target: either the subsequence
domain of a closed list (`Sublist`-style: enumerate sublists) or the
permutation domain (`Perm`-style: same multiset, sorted arrangement
tried first). Named by shape, never by Lean function. -/
inductive RelDom where
  | sub : List Nat → RelDom
  | perm : List Nat → RelDom

/-- One row of the inference dispatch: how a single Lean call node
answers the uniform bound questions. The length/elem questions
recurse over structure; the target questions answer what an equation
`call = closed` forces upon a mentioned target list; the relation
questions answer what a non-`Eq` proposition mentioning the target
forces (subsequence/permutation domains and the like); the peel
question answers what length a same-shape stand-in for the call's
list operand must have, so equations peel through one nesting layer
at a time. -/
structure InferRow where
  inferLengthLower : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferLengthUpper : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemLower : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemUpper : Queries → Array Expr → Nat → MetaM (Option Nat)
  inferElemPool : Queries → Array Expr → Nat → MetaM (Option (List Nat))
  inferTargetExact : FVarId → Array Expr → Expr → MetaM (Option Nat)
  inferTargetLower : FVarId → Array Expr → Expr → MetaM (Option Nat)
  inferTargetUpper : FVarId → Array Expr → Expr → MetaM (Option Nat)
  inferRelLower : FVarId → Queries → Array Expr → Nat → MetaM (Option Nat)
  inferRelUpper : FVarId → Queries → Array Expr → Nat → MetaM (Option Nat)
  inferRelPool : FVarId → Queries → Array Expr → Nat → MetaM (Option (List Nat))
  inferRelDom : FVarId → Array Expr → MetaM (Option RelDom)
  inferPeelLength : Array Expr → Expr → MetaM (Option (Nat × Bool))

/-- Numeric literal (elaborated `OfNat` included). -/
private def natLitOf : Expr → Option Nat :=
  Lynth.FinSearch.Recognize.asNumeral

/-- Explicit list literal spine. -/
private def listLitOf : Expr → Option (List Expr) :=
  Lynth.FinSearch.Recognize.asListLit

/-- Does `e` mention free variable `tgt`? -/
private def mentionsTgt (e : Expr) (tgt : FVarId) : Bool :=
  (e.find? fun | .fvar id => id == tgt | _ => false).isSome

/-- Is `e` exactly the bare target variable? Relation rules only
fire on the bare target: nested occurrences (e.g. under another
call) carry no direct length equation. -/
private def isBareTgt (tgt : FVarId) : Expr → Bool
  | .fvar id => id == tgt
  | _ => false

/-- Last List-typed trailing argument (robust to instance-implicit
arities): the list operand of a call, if any. -/

private def listArgOf (args : Array Expr) : MetaM (Option Expr) := do
  let mut out : Option Expr := none
  for a in args do
    let ty ← try pure (← whnf (← inferType a)) catch _ => continue
    match ty.getAppFn with
    | .const ``List _ => out := some a
    | _ => pure ()
  pure out

/-- Unique Nat literal among arguments, if exactly one. -/
private def uniqNatLit (args : Array Expr) : Option Nat :=
  match args.toList.filterMap natLitOf with
  | [k] => some k
  | _ => none

/-- Numeric literal, seeing through definitions (`ssTarget`-style
closed constants reduce first). Purely syntactic matching would leave
them stuck and the caller would misread a closed value as symbolic. -/
private def natLitW (e : Expr) : MetaM (Option Nat) := do
  let eR ← whnf e
  pure (natLitOf eR)

/-- Closed `List Nat` value, seeing through definitions
(`ssInput`-style constants reduce first) and requiring every element
to be a numeric literal. -/
private def closedNatListW (e : Expr) : MetaM (Option (List Nat)) := do
  let eR ← whnf e
  match listLitOf eR with
  | none => pure none
  | some elts =>
    let vs := elts.filterMap natLitOf
    pure (if vs.length == elts.length then some vs else none)

/-- Closed list length (definitions unfolded). -/
private def closedListLenW (e : Expr) : MetaM (Option Nat) := do
  let eR ← whnf e
  match listLitOf eR with
  | some elts => pure (some elts.length)
  | none => pure none

/-- All Nat literals in an expression subtree (definition-free
syntactic scan: numeric leaves such as erased elements, replacement
values, or index pins). Used only to widen the value pool; every
candidate is still kernel-checked, so over-collection costs search,
never soundness. -/
private def collectNatLits : Expr → List Nat
  | .lit (.natVal n) => [n]
  | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ => [n]
  | .app f a => collectNatLits f ++ collectNatLits a
  | .lam _ _ b _ => collectNatLits b
  | .forallE _ _ b _ => collectNatLits b
  | .letE _ _ v b _ => collectNatLits v ++ collectNatLits b
  | .mdata _ b => collectNatLits b
  | .proj _ _ b => collectNatLits b
  | _ => []

/-- Closed reference lists among a call's arguments: list-typed
operands that do not mention the target and reduce to closed `List
Nat` values (`Sublist`/`Perm` reference sides, possibly behind
definitions). Shared by every relation row. -/
private def closedRefLists (tgt : FVarId) (args : Array Expr) :
    MetaM (List (List Nat)) := do
  let mut out : List (List Nat) := []
  for a in args do
    if mentionsTgt a tgt then continue
    let ty ← try pure (← whnf (← inferType a)) catch _ => continue
    match ty.getAppFn with
    | .const ``List _ =>
      match ← closedNatListW a with
      | some vs => out := vs :: out
      | none => pure ()
    | _ => pure ()
  pure out

/-- No-op relation/peel answers, shared by rows that only contribute
length/element/target inference. -/
private def noRelLo : FVarId → Queries → Array Expr → Nat → MetaM (Option Nat) :=
  fun _ _ _ _ => pure none
private def noRelHi : FVarId → Queries → Array Expr → Nat → MetaM (Option Nat) :=
  fun _ _ _ _ => pure none
private def noRelPool : FVarId → Queries → Array Expr → Nat →
    MetaM (Option (List Nat)) :=
  fun _ _ _ _ => pure none
private def noRelDom : FVarId → Array Expr → MetaM (Option RelDom) :=
  fun _ _ => pure none
private def noPeel : Array Expr → Expr → MetaM (Option (Nat × Bool)) :=
  fun _ _ => pure none

/-- The unknown row: every question unanswered. Default for
unhandled heads, so the dispatch stays total. -/
def unknownRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def nilRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure (some 0),
    inferLengthUpper := fun _ _ _ => pure (some 0),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure (some []),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def consRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure (some 1),
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ args _ => do
      if args.size < 2 then pure none
      else pure (natLitOf args[args.size - 2]!),
    inferElemUpper := fun _ args _ => do
      if args.size < 2 then pure none
      else pure (natLitOf args[args.size - 2]!),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else
        let h := args[args.size - 2]!
        let t := args[args.size - 1]!
        match natLitOf h, ← q.pool t (fuel - 1) with
        | some v, some vs => pure (some (v :: vs))
        | _, some vs => pure (some vs)
        | some v, none => pure (some [v])
        | _, _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def appendRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.lenLo args[args.size - 2]! (fuel - 1)
        let b ← q.lenLo args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => x + y),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.lenHi args[args.size - 2]! (fuel - 1)
        let b ← q.lenHi args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => x + y),
    inferElemLower := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.elemLo args[args.size - 2]! (fuel - 1)
        let b ← q.elemLo args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => min x y),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.elemHi args[args.size - 2]! (fuel - 1)
        let b ← q.elemHi args[args.size - 1]! (fuel - 1)
        pure (a.bind fun x => b.map fun y => max x y),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.size < 2 then pure none
      else do
        let a ← q.pool args[args.size - 2]! (fuel - 1)
        let b ← q.pool args[args.size - 1]! (fuel - 1)
        match a, b with
        | some x, some y => pure (some (x ++ y))
        | some x, none => pure (some x)
        | none, some y => pure (some y)
        | _, _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def reverseRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.lenLo args.back! (fuel - 1),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.lenHi args.back! (fuel - 1),
    inferElemLower := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.elemLo args.back! (fuel - 1),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.elemHi args.back! (fuel - 1),
    inferElemPool := fun q args fuel => do
      if fuel == 0 || args.isEmpty then pure none
      else q.pool args.back! (fuel - 1),
    inferTargetExact := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← closedListLenW closed with
      | some m => pure (some (m, true))
      | none => pure none }

def rangeRow : InferRow :=
  { inferLengthLower := fun _ args _ => pure (uniqNatLit args),
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ _ _ => pure (some 0),
    inferElemUpper := fun _ args _ => do
      pure (uniqNatLit args |>.bind fun n => if n == 0 then none else some (n - 1)),
    inferElemPool := fun _ args _ => do
      pure (uniqNatLit args |>.map List.range),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def replicateRow : InferRow :=
  { inferLengthLower := fun _ args _ => pure (uniqNatLit args),
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ args _ => do
      pure (if args.isEmpty then none else natLitOf args.back!),
    inferElemUpper := fun _ args _ => do
      pure (if args.isEmpty then none else natLitOf args.back!),
    inferElemPool := fun _ args _ => do
      pure (if args.isEmpty then none
        else (natLitOf args.back!).map fun v => [v]),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

def takeRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ args _ => pure (uniqNatLit args),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← closedListLenW closed with
      | some m => pure (some (m, false))
      | none => pure none }

def dropRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else do
        let some l ← listArgOf args | pure none
        let n := uniqNatLit args |>.getD 0
        match ← q.lenHi l (fuel - 1) with
        | some h => pure (some (h - n))
        | none => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun tgt args closed => do
      match ← closedListLenW closed, uniqNatLit args with
      | some m, some n =>
        match ← listArgOf args with
        | some l =>
          if isBareTgt tgt l && m > 0 then
            pure (some (n + m))
          else pure none
        | none => pure none
      | _, _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed, uniqNatLit args with
      | some m, some n =>
        match ← listArgOf args with
        | some l =>
          if isBareTgt tgt l && m > 0 then
            pure (some (n + m))
          else pure none
        | none => pure none
      | _, _ => pure none,
    inferTargetUpper := fun tgt args closed => do
      match ← closedListLenW closed, uniqNatLit args with
      | some m, some n =>
        match ← listArgOf args with
        | some l =>
          if isBareTgt tgt l then
            pure (some (n + m))
          else pure none
        | none => pure none
      | _, _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun args closed => do
      match ← closedListLenW closed, uniqNatLit args with
      | some m, some n =>
        if m > 0 then pure (some (n + m, true)) else pure none
      | _, _ => pure none }

def mapRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenLo l (fuel - 1),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← closedListLenW closed with
      | some m => pure (some (m, true))
      | none => pure none }

def filterRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← closedListLenW closed with
      | some m => pure (some (m, false))
      | none => pure none }

def lengthRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun tgt args closed => do
      match ← natLitW closed with
      | some k =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some k else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← natLitW closed with
      | some k => pure (some (k, true))
      | none => pure none }

def sumRow : InferRow := unknownRow

def countRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← natLitW closed with
      | some k =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some k else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← natLitW closed with
      | some k => pure (some (k, false))
      | none => pure none }

/-- Erase removes at most the first matching element: length drops by
at most one, elements come from the source. -/
def eraseRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => match ← q.lenLo l (fuel - 1) with
          | some lo => pure (some (lo - 1))
          | none => pure none,
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.elemLo l (fuel - 1),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.elemHi l (fuel - 1),
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some (m + 1) else none)
        | none => pure none
      | none => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := noPeel }

/-- Replace preserves length and draws elements from the source
(the two replacement values arrive through pool harvesting). -/
def replaceRow : InferRow :=
  { inferLengthLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenLo l (fuel - 1),
    inferLengthUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.lenHi l (fuel - 1),
    inferElemLower := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.elemLo l (fuel - 1),
    inferElemUpper := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.elemHi l (fuel - 1),
    inferElemPool := fun q args fuel => do
      if fuel == 0 then pure none
      else match ← listArgOf args with
        | none => pure none
        | some l => q.pool l (fuel - 1),
    inferTargetExact := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetLower := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferTargetUpper := fun tgt args closed => do
      match ← closedListLenW closed with
      | some m =>
        match ← listArgOf args with
        | some l => pure (if isBareTgt tgt l then some m else none)
        | none => pure none
      | none => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := noRelHi,
    inferRelPool := noRelPool,
    inferRelDom := noRelDom,
    inferPeelLength := fun _ closed => do
      match ← closedListLenW closed with
      | some m => pure (some (m, true))
      | none => pure none }

/-- Subsequence relation: the target is no longer than any closed
reference it sits inside, and draws values from it. -/
def sublistRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := noRelLo,
    inferRelUpper := fun tgt _ args _ => do
      let mut best : Option Nat := none
      for r in ← closedRefLists tgt args do
        best := some (min (best.getD r.length) r.length)
      pure best,
    inferRelPool := fun tgt _ args _ => do
      let refs ← closedRefLists tgt args
      pure (if refs.isEmpty then none else some refs.flatten),
    inferRelDom := fun tgt args => do
      match ← closedRefLists tgt args with
      | [] => pure none
      | r :: _ => pure (some (.sub r)),
    inferPeelLength := noPeel }

/-- Permutation relation: the target has exactly the reference
length and draws values from it. -/
def permRow : InferRow :=
  { inferLengthLower := fun _ _ _ => pure none,
    inferLengthUpper := fun _ _ _ => pure none,
    inferElemLower := fun _ _ _ => pure none,
    inferElemUpper := fun _ _ _ => pure none,
    inferElemPool := fun _ _ _ => pure none,
    inferTargetExact := fun _ _ _ => pure none,
    inferTargetLower := fun _ _ _ => pure none,
    inferTargetUpper := fun _ _ _ => pure none,
    inferRelLower := fun tgt _ args _ => do
      let mut best : Option Nat := none
      for r in ← closedRefLists tgt args do
        best := some (max (best.getD 0) r.length)
      pure best,
    inferRelUpper := fun tgt _ args _ => do
      let mut best : Option Nat := none
      for r in ← closedRefLists tgt args do
        best := some (min (best.getD r.length) r.length)
      pure best,
    inferRelPool := fun tgt _ args _ => do
      let refs ← closedRefLists tgt args
      pure (if refs.isEmpty then none else some refs.flatten),
    inferRelDom := fun tgt args => do
      match ← closedRefLists tgt args with
      | [] => pure none
      | r :: _ => pure (some (.perm r)),
    inferPeelLength := noPeel }

/-- Length-side detection for comparison conjuncts (`≤`, `<`, `≥`,
`>`): returns the literal bound and whether the `List.length` term is
on the left. Type/instance arguments are ignored; exactly one literal
is required (so `len ≤ len` and two-literal shapes contribute nothing). -/
private def lenSideOf (tgt : FVarId) (args : Array Expr) :
    MetaM (Option (Nat × Bool)) := do
  let mut lenIdx : Option Nat := none
  let mut litIdx : Option Nat := none
  let mut litVal : Nat := 0
  let mut litCount := 0
  for i in List.range args.size do
    let aR ← whnfR args[i]!
    -- NOTE: match on `getAppFn`, not a single `.app`, since `List.length`
    -- carries its implicit type argument (`app (app const ty) as`).
    match aR.getAppFn with
    | .const ``List.length _ =>
      if aR.getAppArgs.any (mentionsTgt · tgt) then lenIdx := some i
    | _ =>
      match ← natLitW args[i]! with
      | some k => litCount := litCount + 1; litIdx := some i; litVal := k
      | none => pure ()
  match lenIdx, litIdx with
  | some li, some gi => pure (if litCount == 1 then some (litVal, li < gi) else none)
  | _, _ => pure none

/-- `l.length ≤ k` / `k ≤ l.length` length bounds. -/
def leRow : InferRow := { unknownRow with
  inferRelUpper := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, true) => pure (some k)
    | _ => pure none,
  inferRelLower := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, false) => pure (some k)
    | _ => pure none }

/-- `l.length < k` / `k < l.length` length bounds (Nat saturation:
`k - 1` at zero stays zero, giving an empty window that the
kernel-checked closer rejects — sound). -/
def ltRow : InferRow := { unknownRow with
  inferRelUpper := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, true) => pure (some (k - 1))
    | _ => pure none,
  inferRelLower := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, false) => pure (some (k + 1))
    | _ => pure none }

/-- `l.length ≥ k` / `k ≥ l.length`: mirror of `≤`. -/
def geRow : InferRow := { unknownRow with
  inferRelUpper := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, false) => pure (some k)
    | _ => pure none,
  inferRelLower := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, true) => pure (some k)
    | _ => pure none }

/-- `l.length > k` / `k > l.length`: mirror of `<`. -/
def gtRow : InferRow := { unknownRow with
  inferRelUpper := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, false) => pure (some (k - 1))
    | _ => pure none,
  inferRelLower := fun tgt _ args _ => do
    match ← lenSideOf tgt args with
    | some (k, true) => pure (some (k + 1))
    | _ => pure none }

/-- Pool from `l.all` with a literal upper-bound predicate: open the
(single) lambda, scan subterms for `x < k` / `x ≤ k` against the bound
variable with closed `k` (finds them under `decide` wrappers and
conjunctions too), and bound elements below the tightest one. -/
private def allBoundPool (tgt : FVarId) (args : Array Expr) :
    MetaM (Option (List Nat)) := do
  -- find the list arg mentioning tgt and a predicate arg
  let mut listOk := false
  let mut predArg : Option Expr := none
  for a in args do
    let aR ← whnfR a
    match aR.getAppFn with
    | .const ``List _ => pure ()
    | _ =>
      if mentionsTgt a tgt then listOk := true
      else match ← natLitW a with
        | some _ => pure ()
        | none =>
          let ty ← try pure (← whnf (← inferType a)) catch _ => pure (Expr.const ``Unit [])
          match ty.getAppFn with
          | .const ``List _ => pure ()
          | _ => predArg := some a
  if !listOk then return none
  match predArg with
  | none => pure none
  | some p =>
    lambdaTelescope p fun xs b => do
      if xs.size != 1 then pure none
      else
        let x := xs[0]!
        let mut best : Option Nat := none
        for s in Lynth.Euf.Procedure.collectSubterms b do
          -- NOTE: match by head name with last-two-args, never by exact
          -- application spine: `<`/`≤` elaborate to `LT.lt`/`LE.le`
          -- (typeclass, type+instance args) or directly to `Nat.lt`/
          -- `Nat.le` (bare sides), depending on context.
          match s.getAppFn with
          | .const fn _ =>
            if fn == ``LT.lt || fn == ``LE.le || fn == ``Nat.lt || fn == ``Nat.le then
              let args := s.getAppArgs
              if 2 ≤ args.size then
                let a := args[args.size - 2]!
                let k := args[args.size - 1]!
                if a == x then match ← natLitW k with
                  | some n =>
                    let n := if fn == ``LT.lt || fn == ``Nat.lt then n else n + 1
                    best := some (min (best.getD n) n)
                  | none => pure ()
          | _ => pure ()
        match best with
        | none => pure none
        | some n => pure (some (List.range n))

def allRow : InferRow := { unknownRow with
  inferRelPool := fun tgt _ args _ => allBoundPool tgt args }

/-- Nodup relation: a duplicate-free list over a finite element type
(`Fin n`, `Bool`) has length at most the cardinality. Only the bare
target counts (nested occurrences carry no direct bound). -/
def nodupRow : InferRow := { unknownRow with
  inferRelUpper := fun tgt _ args _ => do
    for a in args do
      if !isBareTgt tgt a then continue
      else
        let ty ← try pure (← whnfR (← inferType a)) catch _ => continue
        match ty.getAppFn with
        | .const ``List _ =>
          let eargs := ty.getAppArgs
          if eargs.size != 1 then continue
          else
            let et ← whnfR eargs[0]!
            match et.getAppFn with
            | .const ``Fin _ =>
              match et.getAppArgs[0]? with
              | some nExpr =>
                match ← natLitW nExpr with
                | some n => return some n
                | none => continue
              | none => continue
            | .const ``Bool _ => return some 2
            | _ => continue
        | _ => continue
    pure none }

/-- The single dispatcher: every handled Lean function maps to its
inference row. Unknown heads get `unknownRow`. -/
def inferenceRow : Name → InferRow
  | n =>
    if n == ``List.nil then nilRow
    else if n == ``List.cons then consRow
    else if n == ``List.append then appendRow
    else if n == ``HAppend.hAppend then appendRow
    else if n == ``List.reverse then reverseRow
    else if n == ``List.range then rangeRow
    else if n == ``List.replicate then replicateRow
    else if n == ``List.take then takeRow
    else if n == ``List.drop then dropRow
    else if n == ``List.map then mapRow
    else if n == ``List.filter then filterRow
    else if n == ``List.length then lengthRow
    else if n == ``List.sum then sumRow
    else if n == ``List.count then countRow
    else if n == ``List.erase then eraseRow
    else if n == ``List.replace then replaceRow
    else if n == ``List.Sublist then sublistRow
    else if n == ``List.Perm then permRow
    else if n == ``List.all then allRow
    else if n == ``List.Nodup then nodupRow
    else if n == ``LE.le then leRow
    else if n == ``LT.lt then ltRow
    else if n == ``GE.ge then geRow
    else if n == ``GT.gt then gtRow
    else if n == ``Nat.le then leRow
    else if n == ``Nat.lt then ltRow
    else unknownRow

/-- Empty bundle (all unknown): `Inhabited` witness so the
recursive bundle below compiles; never used for real queries. -/
instance : Inhabited Queries where
  default :=
    { lenLo := fun _ _ => pure none,
      lenHi := fun _ _ => pure none,
      elemLo := fun _ _ => pure none,
      elemHi := fun _ _ => pure none,
      pool := fun _ _ => pure none }

/-- The recursive query bundle, parameterized by the row lookup
so no mutual block is needed: each question dispatches on the
head and recurses on strict subterms with shrinking fuel. -/
partial def queriesFrom (rowOf : Name → InferRow) : Queries :=
  { lenLo := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferLengthLower (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    lenHi := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferLengthUpper (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    elemLo := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemLower (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    elemHi := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemUpper (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none,
    pool := fun e fuel =>
      if fuel == 0 then pure none
      else match e.getAppFn with
        | .const fn _ =>
          (rowOf fn).inferElemPool (queriesFrom rowOf) e.getAppArgs (fuel - 1)
        | _ => pure none }

/-- The bundle handed to rows: recursive questions over
`inferenceRow`. -/
def queries : Queries := queriesFrom inferenceRow

/-- Collected bounds on the target list. Reference domains record
closed lists governing the target (`Sublist`/`Perm` sides). -/
structure Bounds where
  lenLo : Nat := 0
  lenHi : Option Nat := none
  pool : List Nat := []
  subRef : Option (List Nat) := none
  permRef : Option (List Nat) := none

/-- Flatten top-level `And` conjunctions. -/
def splitConj : Expr → List Expr
  | .app (.app (.const ``And _) a) b => splitConj a ++ splitConj b
  | e => [e]

/-- Dummy closed list of length `m` (zeros): a same-length stand-in
so an inner call's target methods can fire on nested occurrences.
Elements are meaningless and never harvested for pools. -/
private def dummyLit (m : Nat) : MetaM Expr :=
  mkListLit (mkConst ``Nat []) ((List.range m).map fun _ => mkNatLit 0)

/-- Peel one nesting layer: when `tSide = closed` forces the operand
to a known length `m` (exact shape or lower bound, per the outer
row's own `inferPeelLength`), re-ask the inner heads' target methods
on a same-length dummy. Only the channels the outer shape justifies
run (exact shapes propagate lower and upper; lower-bound shapes
propagate lower only), so each step is sound by the rows' own
meanings. Strict subterms plus fuel guarantee termination. -/
private partial def peelTargets (tgt : FVarId) (tSide : Expr) (m : Nat)
    (exact : Bool) (st : Bounds) (fuel : Nat) : MetaM Bounds := do
  if fuel == 0 then pure st
  else
    let dummy ← dummyLit m
    let mut st := st
    for a in tSide.getAppArgs do
      if mentionsTgt a tgt && !isBareTgt tgt a then
        match a.getAppFn with
        | .const fn _ =>
          let row := inferenceRow fn
          let iargs := a.getAppArgs
          match ← row.inferTargetLower tgt iargs dummy with
          | some n => st := { st with lenLo := max st.lenLo n }
          | none => pure ()
          if exact then
            match ← row.inferTargetUpper tgt iargs dummy with
            | some n =>
              st := { st with lenHi := some (min (st.lenHi.getD n) n) }
            | none => pure ()
          -- deeper layers keep the weaker channel
          st ← peelTargets tgt a m false st (fuel - 1)
        | _ => pure ()
    pure st

/-- Process one `Eq` conjunct: orient target side vs closed side,
ask the target relation methods, harvest literal pools. Anything
unrecognized contributes nothing (the kernel still enforces it
when candidates are checked). -/
def processEq (tgt : FVarId) (a b : Expr) (st : Bounds) : MetaM Bounds := do
  let oriented : Option (Expr × Expr) :=
    if mentionsTgt a tgt && !mentionsTgt b tgt then some (a, b)
    else if mentionsTgt b tgt && !mentionsTgt a tgt then some (b, a)
    else none
  match oriented with
  | none => pure st
  | some (tSide, cSide) =>
    if cSide.hasFVar then pure st
    else
      let cSideR ← whnf cSide
      let mut st := st
      -- pool harvesting: closed list literals contribute elements;
      -- every Nat literal in either side is a candidate value
      -- (erased elements, replacements, indices)
      match ← closedNatListW cSideR with
      | some vs => st := { st with pool := st.pool ++ vs }
      | none => pure ()
      st := { st with pool := st.pool ++ collectNatLits tSide ++ collectNatLits cSideR }
      -- length reasoning by target-side shape
      match tSide with
      | .fvar id =>
        if id == tgt then
          match ← closedNatListW cSideR with
          | some vs =>
            let lo := max st.lenLo vs.length
            let hi := min (st.lenHi.getD vs.length) vs.length
            st := { st with lenLo := lo, lenHi := some hi, pool := st.pool }
          | none => pure ()
        else pure ()
      | _ =>
        match tSide.getAppFn with
        | .const fn _ =>
          let row := inferenceRow fn
          let args := tSide.getAppArgs
          match ← row.inferTargetExact tgt args cSideR with
          | some n =>
            let lo := max st.lenLo n
            let hi := min (st.lenHi.getD n) n
            st := { st with lenLo := lo, lenHi := some hi }
          | none => pure ()
          match ← row.inferTargetLower tgt args cSideR with
          | some n => st := { st with lenLo := max st.lenLo n }
          | none => pure ()
          match ← row.inferTargetUpper tgt args cSideR with
          | some n =>
            let hi := min (st.lenHi.getD n) n
            st := { st with lenHi := some hi }
          | none => pure ()
          -- per-call pool rows supplement literal harvesting
          match ← row.inferElemPool queries args 8 with
          | some vs => st := { st with pool := st.pool ++ vs }
          | none => pure ()
          -- `l.all p = true` sides never reach relation inference
          -- (they route here as `Eq`), so ask the bound pool directly
          match tSide.getAppFn with
          | .const ``List.all _ =>
            -- NOTE: `= true` here is Boolean `Bool.true`, not `Prop`'s `True`
            if cSideR.isConstOf ``Bool.true then
              match ← allBoundPool tgt tSide.getAppArgs with
              | some vs => st := { st with pool := st.pool ++ vs }
              | none => pure ()
            else pure ()
          | _ => pure ()
          -- nested occurrences: peel one layer per the outer row's
          -- own length story (exact shapes propagate both bounds,
          -- lower-bound shapes propagate lower only)
          match ← row.inferPeelLength args cSideR with
          | some (m, exact) => st ← peelTargets tgt tSide m exact st 8
          | none => pure ()
        | _ => pure ()
      pure st

/-- Process one non-`Eq` conjunct mentioning the target
(`Sublist`/`Perm` domains and the like) through the relation
methods. Unknown heads contribute nothing. -/
def processRel (tgt : FVarId) (c : Expr) (st : Bounds) : MetaM Bounds := do
  if !mentionsTgt c tgt then pure st
  else
    match c.getAppFn with
    | .const fn _ =>
      if fn == ``Eq || fn == ``And then pure st
      else
        let row := inferenceRow fn
        let args := c.getAppArgs
        let mut st := st
        match ← row.inferRelLower tgt queries args 8 with
        | some n => st := { st with lenLo := max st.lenLo n }
        | none => pure ()
        match ← row.inferRelUpper tgt queries args 8 with
        | some n =>
          st := { st with lenHi := some (min (st.lenHi.getD n) n) }
        | none => pure ()
        match ← row.inferRelPool tgt queries args 8 with
        | some vs => st := { st with pool := st.pool ++ vs }
        | none => pure ()
        match ← row.inferRelDom tgt args with
        | some (.sub r) =>
          st := { st with pool := st.pool ++ r }
          if st.subRef.isNone then st := { st with subRef := some r }
        | some (.perm r) =>
          st := { st with pool := st.pool ++ r }
          if st.permRef.isNone then st := { st with permRef := some r }
        | none => pure ()
        pure st
    | _ => pure st

/-- Intersect bounds across all conjunctions to a fixpoint
(bounds only tighten, pools only grow; fuel caps the rounds).
`Eq` conjuncts go through target inference, every other shape
through relation inference. -/
def inferBounds (tgt : FVarId) (conjs : List Expr) : MetaM Bounds := do
  let mut st : Bounds := {}
  for _ in List.range 12 do
    let mut st' := st
    for c in conjs do
      let cr ← whnfR c
      match cr.getAppFn with
      | .const ``Eq _ =>
        let args := cr.getAppArgs
        if args.size != 3 then pure ()
        else st' ← processEq tgt args[args.size - 2]! args[args.size - 1]! st'
      | _ => st' ← processRel tgt cr st'
    st := st'
  pure st

/-- All length-`n` lists over `pool`, lexicographic. -/
def allLists : List Nat → Nat → List (List Nat)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | p, n + 1 => (allLists p n).flatMap fun rest => p.map fun v => v :: rest

/-- All sublists (order-preserving subsets) of `xs`. -/
def sublistsOf : List Nat → List (List Nat)
  | [] => [[]]
  | x :: xs => let r := sublistsOf xs; r ++ r.map (x :: ·)

/-- All length-`n` lists over an explicit element pool. -/
def allListsE : List Expr → Nat → List (List Expr)
  | _, 0 => [[]]
  | [], _ + 1 => []
  | p, n + 1 => (allListsE p n).flatMap fun rest => p.map fun v => v :: rest

/-- Length equation on `w`: `w.length = k` (either orientation)
with closed `k`. -/
private def lenEqOf (w : Expr) (e : Expr) : MetaM (Option Nat) := do
  let e ← whnfR e
  match e.getAppFn with
  | .const ``Eq _ =>
    let args := e.getAppArgs
    if args.size < 2 then pure none
    else
      let a := args[args.size - 2]!
      let b := args[args.size - 1]!
      if isLenW w a then
        match ← natLitW b with | some k => pure (some k) | none => pure none
      else if isLenW w b then
        match ← natLitW a with | some k => pure (some k) | none => pure none
      else pure none
  | _ => pure none
where
  /-- `List.length` applied (transitively) to `w`. -/
  isLenW (w side : Expr) : Bool :=
    match side.getAppFn with
    | .const ``List.length _ => side.getAppArgs.any (· == w)
    | _ => false

/-- Inner length from a single universal: `∀ w ∈ tgt, …` with a
length equation on `w` in the body. Exact `Eq` only. -/
private def innerLengthConj (tgt : FVarId) (c : Expr) : MetaM (Option Nat) := do
  let cr ← whnfR c
  match cr with
  | .forallE _ _ _ _ =>
    forallTelescope cr fun xs b => do
      if xs.size != 2 then pure none
      else
        let w := xs[0]!
        let hty ← inferType xs[1]!
        if !((hty.find? (· == w)).isSome && mentionsTgt hty tgt) then pure none
        else lenEqOf w b
  | _ => pure none

/-- Tightest inner length across universals (exact `Eq` only). -/
private def innerLengthOf (tgt : FVarId) (conjs : List Expr) : MetaM (Option Nat) := do
  let mut best : Option Nat := none
  for c in conjs do
    match ← innerLengthConj tgt c with
    | none => pure ()
    | some k => best := some (min (best.getD k) k)
  pure best

/-- Single-shot `DecidablePred` synthesis: `some` instance or `none`
(never throws). Single-line `try` form — nested multiline `try`s
confuse the parser here. -/
private def synthDecPred? (lam : Expr) : TacticM (Option Expr) := do
  try pure (← synthInstance (← mkAppM ``DecidablePred #[lam]))
  catch _ => pure none

/-- Decidable-conjunct filter for an undecidable predicate: synthesize
`DecidablePred` per conjunct once, combine the decidable ones under a
single lambda. `none` ⟹ no usable decidable part (pass everything
through to full close). -/
private def buildDecFilter (predU : Expr) : TacticM (Option (Expr × Expr)) := do
  try
    lambdaTelescope predU fun fvarsU bodyU => do
      if fvarsU.size != 1 then pure (none : Option (Expr × Expr))
      else
        let mut lams : Array Expr := #[]
        for c in splitConj (← whnf bodyU) do
          let lam ← mkLambdaFVars #[fvarsU[0]!] c
          match ← synthDecPred? lam with
          | some _ => lams := lams.push lam
          | none => pure ()
        if lams.isEmpty then pure none
        else
          let mut acc := mkApp lams[0]! fvarsU[0]!
          for lam in lams.toList.drop 1 do
            acc ← mkAppM ``And #[acc, mkApp lam fvarsU[0]!]
          let combined ← mkLambdaFVars #[fvarsU[0]!] acc
          match ← synthDecPred? combined with
          | some dinst => pure (some (combined, dinst))
          | none => pure none
  catch _ => pure none

/-- Kernel-check each pre-built candidate value in turn: assign it,
and run the shared kernel-checked closer. Yields when none closes
(wrong inferences only ever miss, never mis-prove). -/
private def tryVals (shape : Lynth.Witness.WitShape)
    (cands : List Expr) : TacticM ProcedureOutcome := do
  let others ← getUnsolvedGoals
  let snap0 ← saveState
  let uns ← Lynth.Witness.unfoldSideDefs
  -- fast path: synthesize `DecidablePred` once for the unfolded
  -- predicate; per candidate kernel-evaluate `decide` (no TC synthesis,
  -- no snapshots for rejects). Falls back to full close per candidate
  -- when the predicate shape is undecidable. NOTE: re-classify after
  -- unfolding — `shape.pred` is the folded form, and bare `whnf` stops
  -- at its outer lambda without exposing the body.
  let predU ← do
    let goal ← getMainTarget
    match ← Lynth.Witness.classify goal with
    | none => whnf shape.pred
    | some shape' => whnf shape'.pred
  let dpred? : Option Expr ← try
      pure (← synthInstance (← mkAppM ``DecidablePred #[predU]))
    catch _ => pure none
  -- When the whole predicate is undecidable (universals), still
  -- kernel-filter by its decidable conjuncts (reject only on kernel
  -- `false`; stuck evaluation never rejects — misses, never
  -- mis-proves). Pure fast-reject: full close still decides.
  let decFilter? : Option (Expr × Expr) ← match dpred? with
    | some _ => pure none
    | none => buildDecFilter predU
  for wv in cands do
    let hit ← match dpred? with
      | some dpred =>
        let instWv := mkApp dpred wv
        let d := mkApp (mkApp (mkConst ``Decidable.decide []) (mkApp predU wv)) instWv
        match ← whnf d with
        | .const ``Bool.false _ => pure false
        | _ => pure true
      | none =>
        match decFilter? with
        | none => pure true
        | some (combined, dinst) =>
          let instWv := mkApp dinst wv
          let d := mkApp (mkApp (mkConst ``Decidable.decide []) (mkApp combined wv)) instWv
          match ← whnf d with
          | .const ``Bool.false _ => pure false
          | _ => pure true
    if hit then
      let snapshot ← saveState
      try
        let mvar ← getMainGoal
        let sideTy := mkApp shape.pred wv
        let sidePrf ← mkFreshExprSyntheticOpaqueMVar sideTy
        let val ← shape.mkVal wv sidePrf
        mvar.assign val
        replaceMainGoal (sidePrf.mvarId! :: others.filter (· != mvar))
        -- shared kernel-checked closer (unfolds re-applied, no discovery)
        Lynth.Witness.applySideUnfolds uns
        if ← Lynth.Witness.closeSideNoUnfold then
          return .success
        restoreState snapshot
      catch _ =>
        restoreState snapshot
    else pure ()
  restoreState snap0
  return .failure []

private def tryCands (shape : Lynth.Witness.WitShape)
    (cands : List (List Nat)) : TacticM ProcedureOutcome := do
  let vals ← cands.mapM fun w =>
    mkListLit (mkConst ``Nat []) (w.map mkNatLit)
  tryVals shape vals

/-- Shared outer enumeration over pre-built element values:
length window from existing rows, total cap, kernel-checked closer. -/
private def outerEnum (shape : Lynth.Witness.WitShape) (elemTy : Expr)
    (elemVals : List Expr) (tgt : FVarId) (conjs : List Expr) :
    TacticM ProcedureOutcome := do
  let st ← inferBounds tgt conjs
  match st.lenHi with
  | none => return .failure []
  | some hi =>
    if st.lenLo > hi then return .failure []
    else if 8 < hi then return .failure []
    else
      let total := (List.range (hi - st.lenLo + 1)).foldl
        (fun acc n => acc + elemVals.length ^ (st.lenLo + n)) 0
      if total == 0 || 2000000 < total then
        return .failure []
      else
        let cands := (List.range (hi - st.lenLo + 1)).flatMap
          fun n => allListsE elemVals (st.lenLo + n)
        let candsVals ← cands.mapM fun w => mkListLit elemTy w
        tryVals shape candsVals

/-- Which `Prod` component (`true` = first) `a` projects from `w`,
if any (named or anonymous projections). -/
private def projCompOf (w a : Expr) : Option Bool := do
  match a.getAppFn with
  | .const n _ =>
    let args := a.getAppArgs
    match args.back? with
    | some x =>
      if x != w then none
      else if n == ``Prod.fst then some true
      else if n == ``Prod.snd then some false
      else none
    | none => none
  | _ =>
    match a with
    | .proj _ idx x =>
      if x != w then none
      else if idx == 0 then some true
      else if idx == 1 then some false
      else none
    | _ => none

/-- Component upper bounds (exclusive) from one universal over our
list: `∀ w ∈ tgt, …w.1… ⋈ k…` with closed `k`. -/
private def pairBoundsConj (tgt : FVarId) (c : Expr) :
    MetaM (Option Nat × Option Nat) := do
  let cr ← whnfR c
  match cr with
  | .forallE _ _ _ _ =>
    forallTelescope cr fun xs b => do
      if xs.size != 2 then pure (none, none)
      else
        let w := xs[0]!
        let hty ← inferType xs[1]!
        if !((hty.find? (· == w)).isSome && mentionsTgt hty tgt) then
          pure (none, none)
        else
          let mut h1 : Option Nat := none
          let mut h2 : Option Nat := none
          for s in Lynth.Euf.Procedure.collectSubterms b do
            match s.getAppFn with
            | .const fn _ =>
              if fn == ``LT.lt || fn == ``LE.le || fn == ``Nat.lt || fn == ``Nat.le then
                let args := s.getAppArgs
                if args.size < 2 then pure ()
                else
                  let a := args[args.size - 2]!
                  let k := args[args.size - 1]!
                  match projCompOf w a with
                  | none => pure ()
                  | some first =>
                    match ← natLitW k with
                    | none => pure ()
                    | some n =>
                      let n := if fn == ``LT.lt || fn == ``Nat.lt then n else n + 1
                      if first then h1 := some (min (h1.getD n) n)
                      else h2 := some (min (h2.getD n) n)
            | _ => pure ()
          pure (h1, h2)
  | _ => pure (none, none)

/-- Tightest component bounds across universals. -/
private def pairBoundsOf (tgt : FVarId) (conjs : List Expr) :
    MetaM (Option Nat × Option Nat) := do
  let mut h1 : Option Nat := none
  let mut h2 : Option Nat := none
  for c in conjs do
    let (a, b) ← pairBoundsConj tgt c
    match a with
    | none => pure ()
    | some n => h1 := some (min (h1.getD n) n)
  for c in conjs do
    let (_, b) := ← pairBoundsConj tgt c
    match b with
    | none => pure ()
    | some n => h2 := some (min (h2.getD n) n)
  pure (h1, h2)

/-- Positional pins from `idxOf?` equations: `l.idxOf? v = some i`
with `l` our bare target and closed `v`, `i` pins value `v` at index
`i` (and forces length `≥ i+1`). Either orientation. -/
private def idxPinsOf (tgt : FVarId) (conjs : List Expr) :
    MetaM (List (Nat × Nat)) := do
  let mut pins : List (Nat × Nat) := []
  for c in conjs do
    let cr ← whnfR c
    match cr.getAppFn with
    | .const ``Eq _ =>
      let args := cr.getAppArgs
      if args.size < 2 then pure ()
      else
        let a := args[args.size - 2]!
        let b := args[args.size - 1]!
        -- idxOf-side has head `List.idxOf?`, some-side head `Option.some`
        let tryDir (x y : Expr) : MetaM (Option (Nat × Nat)) := do
          match x.getAppFn with
          | .const ``List.idxOf? _ =>
            let xargs := x.getAppArgs
            let mut foundL : Bool := false
            let mut val : Option Nat := none
            for xa in xargs do
              match xa with
              | .fvar id => if id == tgt then foundL := true else pure ()
              | _ =>
                match ← natLitW xa with
                | some k => val := some k
                | none => pure ()
            match foundL, val with
            | true, some v =>
              let yr ← whnfR y
              match yr.getAppFn with
              | .const ``Option.some _ =>
                match yr.getAppArgs.back? with
                | some i =>
                  match ← natLitW i with
                  | some n => pure (some (n, v))
                  | none => pure none
                | none => pure none
              | _ => pure none
            | _, _ => pure none
          | _ => pure none
        let r1 ← tryDir a b
        match r1 with
        | some p => pins := if p ∈ pins then pins else p :: pins
        | none =>
          let r2 ← tryDir b a
          match r2 with
          | some p => pins := if p ∈ pins then pins else p :: pins
          | none => pure ()
    | _ => pure ()
  pure pins

/-- Positional enumeration: fix pinned indices, enumerate the rest
over the (widened-superset) pool within the length window. Falls back
to the flat paths when there are no pins. -/
private def tryPositional (shape : Lynth.Witness.WitShape) (tgt : FVarId)
    (conjs : List Expr) (st : Bounds) (pool : List Nat) :
    TacticM ProcedureOutcome := do
  let pins ← idxPinsOf tgt conjs
  if pins.isEmpty then return .failure []
  match st.lenHi with
  | none => return .failure []
  | some hi =>
    -- widen to a superset pool (sound: superset can't miss)
    let pool ← match pool.max? with
      | none => pure pool
      | some m => pure (if 64 < m then pool else (List.range (m + 1)).eraseDups)
    -- lengths must accommodate the highest pin; cap loop like flat paths
    let minLen := pins.foldl (fun acc p => max acc (p.1 + 1)) st.lenLo
    if hi < minLen then return .failure []
    else if 64 < hi then return .failure []
    else
      -- assignments to free positions per length; count completed
      -- candidates against the cap, but still try whatever was built
      -- (early exit on success covers the common case)
      let mut cands : Array Expr := #[]
      let mut total := 0
      for len in List.range (hi - minLen + 1) do
        let n := minLen + len
        -- start from pinned assignments, extend over free positions
        let mut assigns : Array (List (Nat × Nat)) := #[[]]
        for i in List.range n do
          match pins.find? fun p => p.1 == i with
          | some (_, v) =>
            assigns := assigns.map fun a => a ++ [(i, v)]
          | none =>
            let mut next : Array (List (Nat × Nat)) := #[]
            for a in assigns do
              for v in pool do
                next := next.push (a ++ [(i, v)])
            assigns := next
        for a in assigns do
          if 200000 < total then break
          -- values in index order (assignments built ascending)
          let vs := a.map Prod.snd
          total := total + 1
          cands := cands.push (← mkListLit (mkConst ``Nat []) (vs.map mkNatLit))
      if cands.isEmpty then return .failure []
      else tryVals shape cands.toList

/-- Nested finite lists (`List (List Bool)`, `List (List (Fin n))`):
inner length from universals, complete finite inner enumeration,
outer by the length window. Inner values must be finite scalars
(`Bool`/`Fin`); anything else yields. -/
private def runNested (shape : Lynth.Witness.WitShape) (outerElem : Expr) :
    TacticM ProcedureOutcome := do
  let et ← whnfR outerElem
  let beta ← match et.getAppArgs[0]? with
    | none => return .failure []
    | some b => whnfR b
  let betaVals : List Expr ← match beta.getAppFn with
    | .const ``Bool _ => pure [mkConst ``Bool.false, mkConst ``Bool.true]
    | .const ``Fin _ =>
      match beta.getAppArgs[0]? with
      | none => return .failure []
      | some nExpr => match ← natLitW nExpr with
        | none => return .failure []
        | some n =>
          if 64 < n then return .failure []
          else do
            let arr ← (List.range n).toArray.filterMapM fun i => do
              try
                let iLit := mkNatLit i
                let hlt ← mkAppM ``LT.lt #[iLit, mkNatLit n]
                let pf ← mkDecideProof hlt
                some <$> mkAppM ``Fin.mk #[iLit, pf]
              catch _ => pure none
            pure arr.toList
    | _ => return .failure []
  if betaVals.isEmpty then return .failure []
  let pred ← whnf shape.pred
  match pred with
  | .lam _ _ _ _ =>
    lambdaTelescope pred fun fvars body => do
      if fvars.size != 1 then return .failure []
      else
        let body ← whnf body
        match fvars[0]! with
        | .fvar tgt =>
          let fty ← whnfR (← inferType fvars[0]!)
          match fty.getAppFn with
          | .const ``List _ =>
            let conjs := splitConj body
            let innerK? ← innerLengthOf tgt conjs
            match innerK? with
            | none => return .failure []
            | some k =>
              if 8 < k then return .failure []
              else
                let inners := allListsE betaVals k
                let st ← inferBounds tgt conjs
                match st.lenHi with
                | none => return .failure []
                | some hi =>
                  if st.lenLo > hi then return .failure []
                  else if 8 < hi then return .failure []
                  else
                    let total := (List.range (hi - st.lenLo + 1)).foldl
                      (fun acc n => acc + inners.length ^ (st.lenLo + n)) 0
                    if total == 0 || 2000000 < total then
                      return .failure []
                    else do
                      let innerLits ← inners.mapM fun w => mkListLit beta w
                      let cands := (List.range (hi - st.lenLo + 1)).flatMap
                        fun n => allListsE innerLits (st.lenLo + n)
                      let candsVals ← cands.mapM fun w => mkListLit outerElem w
                      tryVals shape candsVals
          | _ => return .failure []
        | _ => return .failure []
  | _ => return .failure []
/-- `List (Nat × Nat)` with component bounds from universals:
pair pool by ranges, outer by the length window. -/
private def runPair (shape : Lynth.Witness.WitShape) (pairTy : Expr) :
    TacticM ProcedureOutcome := do
  let pred ← whnf shape.pred
  match pred with
  | .lam _ _ _ _ =>
    lambdaTelescope pred fun fvars body => do
      if fvars.size != 1 then return .failure []
      else
        let body ← whnf body
        match fvars[0]! with
        | .fvar tgt =>
          let fty ← whnfR (← inferType fvars[0]!)
          match fty.getAppFn with
          | .const ``List _ =>
            let conjs := splitConj body
            let (h1?, h2?) ← pairBoundsOf tgt conjs
            match h1?, h2? with
            | some n1, some n2 =>
              let mut pool : List Expr := []
              for i in List.range n1 do
                for j in List.range n2 do
                  pool := pool ++ [← Lynth.Witness.mkProdVal
                    (mkConst ``Nat []) (mkConst ``Nat []) (mkNatLit i) (mkNatLit j)]
              outerEnum shape pairTy pool tgt conjs
            | _, _ => return .failure []
          | _ => return .failure []
        | _ => return .failure []
  | _ => return .failure []

/-- Product of lists (`List Nat × List Nat`): total-length-ascending
pair enumeration over the pool (widened like the scalar path).
No component bounds needed: the total count cap + kernel-checked
closer keep it sound and bounded. -/
private def runProdPair (shape : Lynth.Witness.WitShape) : TacticM ProcedureOutcome := do
  let pred ← whnf shape.pred
  match pred with
  | .lam _ _ _ _ =>
    lambdaTelescope pred fun fvars body => do
      if fvars.size != 1 then return .failure []
      else
        let body ← whnf body
        match fvars[0]! with
        | .fvar tgt =>
          let fty ← whnfR (← inferType fvars[0]!)
          match fty.getAppFn with
          | .const ``Prod _ =>
            let st ← inferBounds tgt (splitConj body)
            let pool := st.pool.eraseDups
            -- widen like the scalar path when literals suggest 0..max
            let pool ← match pool.max? with
              | none => pure pool
              | some m =>
                if 11 < m then pure pool
                else
                  let wide := List.range (m + 1)
                  pure (if wide.eraseDups == pool then pool else wide)
            if pool.isEmpty then return .failure []
            else if 12 < pool.length then return .failure []
            else
              -- total-length-ascending pairs, capped count
              let mut cands : Array Expr := #[]
              let mut total := 0
              let mut stop := false
              for T in List.range 17 do
                if stop then break
                for l1 in List.range (T + 1) do
                  if stop then break
                  let l2 := T - l1
                  for w1 in allLists pool l1 do
                    if stop then break
                    for w2 in allLists pool l2 do
                      total := total + 1
                      if 200000 < total then
                        stop := true
                        break
                      else
                        let v1 ← mkListLit (mkConst ``Nat []) (w1.map mkNatLit)
                        let v2 ← mkListLit (mkConst ``Nat []) (w2.map mkNatLit)
                        cands := cands.push (← Lynth.Witness.mkProdVal
                          (mkConst ``Nat []) (mkConst ``Nat []) v1 v2)
              tryVals shape cands.toList
          | _ => return .failure []
        | _ => return .failure []
  | _ => return .failure []
/-- `List (Fin n)` case: length-window enumeration over all Fin values.
Mirrors the `List Nat` preamble (telescope + `List` check); no pool is
needed since the element type itself is finite. -/
private def runFin (shape : Lynth.Witness.WitShape) (finTy : Expr) (n : Nat) :
    TacticM ProcedureOutcome := do
  let pred ← whnf shape.pred
  match pred with
  | .lam _ _ _ _ =>
    lambdaTelescope pred fun fvars body => do
      if fvars.size != 1 then return .failure []
      else
        let body ← whnf body
        match fvars[0]! with
        | .fvar tgt =>
          let fty ← whnfR (← inferType fvars[0]!)
          match fty.getAppFn with
          | .const ``List _ =>
            let st ← inferBounds tgt (splitConj body)
            -- Cardinality bounds (`Nodup` over `Fin n`) can hide inside
            -- folded puzzle defs (`validPath p`): when the folded pass
            -- yields no upper bound, unfold once and re-infer.
            -- Fallback only — folded behavior is unchanged.
            let st ← match st.lenHi with
              | some _ => pure st
              | none => do
                let _ ← Lynth.Witness.unfoldSideDefs
                let goal ← getMainTarget
                match ← Lynth.Witness.classify goal with
                | none => pure st
                | some shapeU =>
                  let predU ← whnf shapeU.pred
                  match predU with
                  | .lam _ _ _ _ =>
                    lambdaTelescope predU fun fvarsU bodyU => do
                      if fvarsU.size != 1 then pure st
                      else
                        let bodyU ← whnf bodyU
                        match fvarsU[0]! with
                        | .fvar tgtU => inferBounds tgtU (splitConj bodyU)
                        | _ => pure st
                  | _ => pure st
            match st.lenHi with
            | none =>
              return .failure []
            | some hi =>
              if st.lenLo > hi then return .failure []
              else if 8 < hi then return .failure []
              else
                let vals ← (List.range n).toArray.filterMapM fun i => do
                  try
                    let iLit := mkNatLit i
                    let hlt ← mkAppM ``LT.lt #[iLit, mkNatLit n]
                    let pf ← mkDecideProof hlt
                    some <$> mkAppM ``Fin.mk #[iLit, pf]
                  catch _ => pure none
                let total := (List.range (hi - st.lenLo + 1)).foldl
                  (fun acc k => acc + vals.size ^ (st.lenLo + k)) 0
                if total == 0 || Detect.maxListCand < total then
                  return .failure []
                else
                  let cands := (List.range (hi - st.lenLo + 1)).flatMap
                    fun k => allListsE vals.toList (st.lenLo + k)
                  let candsVals ← cands.mapM fun w => mkListLit finTy w
                  tryVals shape candsVals
          | _ => return .failure []
        | _ => return .failure []
  | _ => return .failure []

/-- List synthesis over `List Nat`: infer exact length plus a finite
value pool, enumerate, and kernel-check each candidate. Yields on
anything else (other domains belong to earlier procedures). -/
def run : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  let some shape ← Lynth.Witness.classify goal
    | return .failure []
  -- only `List Nat` domains reach the inference fixpoint
  let domR ← whnfR shape.dom
  match domR.getAppFn with
  | .const ``Prod _ =>
    -- product-of-lists domain (`List Nat × List Nat`): pair enumeration
    let dargs := domR.getAppArgs
    if dargs.size != 2 then return .failure []
    else
      let a ← whnfR dargs[0]!
      let b ← whnfR dargs[1]!
      match a.getAppFn, b.getAppFn with
      | .const ``List _, .const ``List _ =>
        let aa := a.getAppArgs
        let ba := b.getAppArgs
        if aa.size != 1 || ba.size != 1 then return .failure []
        else
          let ea ← whnfR aa[0]!
          let eb ← whnfR ba[0]!
          match ea, eb with
          | .const ``Nat _, .const ``Nat _ => return ← runProdPair shape
          | _, _ => return .failure []
      | _, _ => return .failure []
  | .const ``List _ =>
    let dargs := domR.getAppArgs
    if dargs.size != 1 then return .failure []
    else
      let et ← whnfR dargs[0]!
      match et with
      | .const ``Nat _ =>
        let pred ← whnf shape.pred
        match pred with
        | .lam _ _ _ _ =>
          lambdaTelescope pred fun fvars body => do
            if fvars.size != 1 then return .failure []
            else
              -- the body may apply a user definition (`tdValid l`);
              -- unfold once so conjunctions/equations are visible
              let body ← whnf body
              match fvars[0]! with
              | .fvar tgt =>
                let fty ← whnfR (← inferType fvars[0]!)
                match fty.getAppFn with
                | .const ``List _ =>
                  let st ← inferBounds tgt (splitConj body)
                  let pool := st.pool.eraseDups
                  -- positional pins first (idxOf?-style); falls through
                  -- silently when there are none
                  match ← tryPositional shape tgt (splitConj body) st pool with
                  | .success => return .success
                  | .failure _ => pure ()
                  match st.subRef with
                  | some r =>
                    -- subsequence domain: enumerate sublists of the
                    -- closed reference, filtered to the length window
                    if 20 < r.length then return .failure []
                    else
                      let hi := st.lenHi.getD r.length
                      let cands := (sublistsOf r).filter fun w =>
                        st.lenLo ≤ w.length ∧ w.length ≤ hi
                      if Detect.maxListCand < cands.length then
                        return .failure []
                      else return ← tryCands shape cands
                  | none =>
                    match st.permRef with
                    | some _ =>
                      -- permutation domain: the sorted arrangement
                      -- first (covers sortedness-coupled goals in one
                      -- kernel check), then bounded enumeration
                      match st.lenHi with
                      | none => return .failure []
                      | some n =>
                        if st.lenLo != n then return .failure []
                        else if pool.isEmpty then return .failure []
                        else
                          if pool.length == n then
                            match ← tryCands shape [pool.mergeSort] with
                            | .success => return .success
                            | .failure _ => pure ()
                          if 12 < pool.length then return .failure []
                          else if 8 < n then return .failure []
                          else
                            let total := pool.length ^ n
                            if total == 0 || Detect.maxListCand < total then
                              return .failure []
                            else return ← tryCands shape (allLists pool n)
                    | none =>
                      -- length cap: inferred, else defaulted from pool size
                      -- (small pools only; the shared body re-checks all
                      -- gates, so this only ever enables new searches).
                      let hiD : Option Nat :=
                        if 8 < pool.length then none
                        else
                          let hs := (List.range 9).filter fun h =>
                            st.lenLo ≤ h &&
                            (List.range (h - st.lenLo + 1)).foldl
                              (fun acc n => acc + pool.length ^ (st.lenLo + n)) 0
                              ≤ Detect.maxListCand
                          hs.getLast?
                      match st.lenHi.or hiD with
                      | none => return .failure []
                      | some hi =>
                        if st.lenLo > hi then return .failure []
                        else if pool.isEmpty then return .failure []
                        else if 12 < pool.length then return .failure []
                        else if 8 < hi then return .failure []
                        else
                          let total := (List.range (hi - st.lenLo + 1)).foldl
                            (fun acc n => acc + pool.length ^ (st.lenLo + n)) 0
                          if total == 0 || Detect.maxListCand < total then
                            return .failure []
                          else
                            let cands := (List.range (hi - st.lenLo + 1)).flatMap
                              fun n => allLists pool (st.lenLo + n)
                            match ← tryCands shape cands with
                            | .success => return .success
                            | .failure _ => pure ()
                            -- retry over the widened 0..max pool:
                            -- preimages (map images, erased elements)
                            -- live below the largest seen literal
                            match pool.max? with
                            | none => return .failure []
                            | some m =>
                              if 11 < m then return .failure []
                              else
                                let wide := List.range (m + 1)
                                if wide.eraseDups == pool then
                                  return .failure []
                                else
                                  let totalW := (List.range (hi - st.lenLo + 1)).foldl
                                    (fun acc n => acc + wide.length ^ (st.lenLo + n)) 0
                                  if totalW == 0 || Detect.maxListCand < totalW then
                                    return .failure []
                                  else
                                    let candsW := (List.range (hi - st.lenLo + 1)).flatMap
                                      fun n => allLists wide (st.lenLo + n)
                                    return ← tryCands shape candsW
                | _ => return .failure []
              | _ => return .failure []
        | _ => pure (.failure [])
      | .app (.const ``Fin _) _ =>
        match et.getAppArgs[0]? with
        | none => return .failure []
        | some nExpr =>
          match ← natLitW nExpr with
          | none => return .failure []
          | some n => return ← runFin shape dargs[0]! n
      | .app (.const ``List _) _ =>
        -- nested finite lists (`List (List Bool)` etc.): inner length
        -- from `∀ w ∈ tgt, w.length = k` universals, inner values by
        -- complete finite enumeration, outer by the length window
        return ← runNested shape dargs[0]!
      | .app (.app (.const ``Prod _) α) β => do
        -- pair elements over `Nat` with component bounds from
        -- universals (`∀ w ∈ tgt, w.1 < k …`)
        let α ← whnfR α
        let β ← whnfR β
        match α, β with
        | .const ``Nat _, .const ``Nat _ => return ← runPair shape dargs[0]!
        | _, _ => return .failure []
      | _ => return .failure []
  | _ => return .failure []

end Lynth.FinSearch.ListInfer
