import Lynth.Sat.Syntax

/-!
Finite-domain internal language: terms and propositions over finite
cardinalities.

`FTerm` values range over `0 .. card-1`. `FProp` covers equality,
disequality, `AllDifferent`, order comparisons, boolean structure and
exact-cardinality (`exactK`, for counting constraints like Star Battle
row counts or Towers visibility). `eval` is the reference semantics
used by differential tests; `Encode` compiles the same language to
CNF. There are deliberately no arithmetic operators yet: comparisons
go through comparator circuits in the encoder.
-/
namespace Lynth.FinSearch

open Lynth.Sat

/-- Finite-domain term: variable or literal at a cardinality. -/
inductive FTerm where
  | var : Nat → Nat → FTerm
  | lit : Nat → Nat → FTerm
  deriving Repr, DecidableEq

/-- Cardinality of a term. -/
def cardOf : FTerm → Nat
  | .var c _ => c
  | .lit c _ => c

/-- Value of a term under an assignment (`var id → value`). -/
def evalTerm (t : FTerm) (assign : Nat → Nat) : Nat :=
  match t with
  | .var c a => assign a % c
  | .lit c v => v % c

/-- Finite-domain proposition. -/
inductive FProp where
  | eq : FTerm → FTerm → FProp
  | ne : FTerm → FTerm → FProp
  | distinct : List FTerm → FProp
  | lt : FTerm → FTerm → FProp
  | le : FTerm → FTerm → FProp
  | and : List FProp → FProp
  | or : List FProp → FProp
  | not : FProp → FProp
  | tru : FProp
  | fls : FProp
  | exactK : List FProp → Nat → FProp
  deriving Repr

mutual
/-- Reference evaluation of propositions. -/
def evalProp : FProp → (Nat → Nat) → Bool
  | .eq a b, v => decide (evalTerm a v == evalTerm b v)
  | .ne a b, v => decide (evalTerm a v != evalTerm b v)
  | .distinct ts, v =>
    let vs := ts.map fun t => evalTerm t v
    vs.length == vs.eraseDups.length
  | .lt a b, v => decide (evalTerm a v < evalTerm b v)
  | .le a b, v => decide (evalTerm a v ≤ evalTerm b v)
  | .and ps, v => evalAll ps v
  | .or ps, v => evalAny ps v
  | .not p, v => !(evalProp p v)
  | .tru, _ => true
  | .fls, _ => false
  | .exactK ps k, v =>
    ((ps.filter fun p => evalProp p v).length) == k

def evalAll : List FProp → (Nat → Nat) → Bool
  | [], _ => true
  | p :: ps, v => evalProp p v && evalAll ps v

def evalAny : List FProp → (Nat → Nat) → Bool
  | [], _ => false
  | p :: ps, v => evalProp p v || evalAny ps v
end

end Lynth.FinSearch
