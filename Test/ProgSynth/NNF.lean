-- Synquid demo/NNF.sq, translated: synthesize `toNNF`.
-- TODO: failing until function synthesis over inductive domains lands.
import Lynth

/-- Variable keys (Synquid's abstract `Id`, instantiated to `Nat`). -/
abbrev VarId := Nat

inductive Expr where
  | var : VarId → Expr
  | neg : Expr → Expr
  | conj : Expr → Expr → Expr
  | disj : Expr → Expr → Expr
  | impl : Expr → Expr → Expr

inductive NExpr where
  | atom : VarId → Bool → NExpr
  | nand : NExpr → NExpr → NExpr
  | nor : NExpr → NExpr → NExpr

/-- Evaluation of an unrestricted formula under a store. -/
def eval (store : VarId → Bool) : Expr → Bool
  | .var x => store x
  | .neg e => !eval store e
  | .conj a b => eval store a && eval store b
  | .disj a b => eval store a || eval store b
  | .impl a b => !eval store a || eval store b

/-- Evaluation of an NNF formula under a store. -/
def neval (store : VarId → Bool) : NExpr → Bool
  | .atom x neg => if neg then !store x else store x
  | .nand a b => neval store a && neval store b
  | .nor a b => neval store a || neval store b

/-- Node count of an NNF formula (Synquid's `size`, NNF side). -/
def nsize : NExpr → Nat
  | .atom _ _ => 1
  | .nand a b => 1 + nsize a + nsize b
  | .nor a b => 1 + nsize a + nsize b

/-- The goal: a function mapping every formula to an NNF formula that
evaluates identically, for every store. -/
def toNNF
    : { f : Expr → NExpr //
        ∀ (store : VarId → Bool) (e : Expr), neval store (f e) = eval store e } := by
  lynth

/-- 30-node expression mixing all constructors: 13 `.var`, 5 `.neg`,
4 `.conj`, 4 `.disj`, 4 `.impl` (= 30 nodes, depth 13). -/
def e30 : Expr :=
  let l0 : Expr := .var 0
  let l1 : Expr := .neg l0
  let l2 : Expr := .conj l1 (.var 1)
  let l3 : Expr := .disj l2 (.var 2)
  let l4 : Expr := .impl l3 (.neg (.var 3))
  let l5 : Expr := .conj l4 (.var 4)
  let l6 : Expr := .disj l5 (.var 5)
  let l7 : Expr := .impl l6 (.neg (.var 6))
  let l8 : Expr := .conj l7 (.var 7)
  let l9 : Expr := .disj l8 (.var 8)
  let l10 : Expr := .impl l9 (.neg (.var 9))
  let l11 : Expr := .conj l10 (.var 10)
  let l12 : Expr := .disj l11 (.var 11)
  let l13 : Expr := .impl l12 (.neg (.var 12))
  l13

-- Correct on the 30-node input:
#guard neval (fun i : VarId => i % 2 == 0) (toNNF.1 e30)
     = eval (fun i : VarId => i % 2 == 0) e30

-- No exponential blowup: 30 nodes in, |NNF| ≤ 1024 out (any sane
-- linear/quadratic translation fits; an exponential one needs ≥ 2^14).
#guard nsize (toNNF.1 e30) ≤ 1024

/-- info: 'toNNF' depends on axioms: [propext] -/
#guard_msgs in
#print axioms toNNF
