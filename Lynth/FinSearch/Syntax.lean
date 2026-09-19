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

/-- Finite-domain proposition.
`atom` is an opaque theory piece for the lazy loop: a big fragment
kept out of the CNF, checked against candidate models by `evalProp`
and learned back as blocking clauses. Never nested inside another
`atom` (the splitter only cuts non-`atom` pieces). -/
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
  | atom : Nat → FProp
  deriving Repr

instance : Inhabited FProp := ⟨.tru⟩

/-- Boolean equality on `FProp` (needed by the `SVal` `ite` smart
constructors' identical-branch collapse). Structural; `FTerm`
already has `DecidableEq` so `==` works there. -/
def propBeq : FProp → FProp → Bool
  | .eq a b, .eq c d => a == c && b == d
  | .ne a b, .ne c d => a == c && b == d
  | .distinct ts, .distinct us => ts == us
  | .lt a b, .lt c d => a == c && b == d
  | .le a b, .le c d => a == c && b == d
  | .and ps, .and qs => propListBeq ps qs
  | .or ps, .or qs => propListBeq ps qs
  | .not p, .not q => propBeq p q
  | .tru, .tru => true
  | .fls, .fls => true
  | .exactK ps k, .exactK qs m => propListBeq ps qs && k == m
  | .atom i, .atom j => i == j
  | _, _ => false
where propListBeq : List FProp → List FProp → Bool
  | [], [] => true
  | p :: ps, q :: qs => propBeq p q && propListBeq ps qs
  | _, _ => false

instance : BEq FProp where
  beq := propBeq

mutual
/-- Reference evaluation of propositions. `av` answers opaque `atom`
ids (the lazy loop evaluates atom contents separately, so the top
level never needs it; tests pass `fun _ => false`). -/
def evalProp : FProp → (Nat → Nat) → (Nat → Bool) → Bool
  | .eq a b, v, _ => decide (evalTerm a v == evalTerm b v)
  | .ne a b, v, _ => decide (evalTerm a v != evalTerm b v)
  | .distinct ts, v, _ =>
    let vs := ts.map fun t => evalTerm t v
    vs.length == vs.eraseDups.length
  | .lt a b, v, _ => decide (evalTerm a v < evalTerm b v)
  | .le a b, v, _ => decide (evalTerm a v ≤ evalTerm b v)
  | .and ps, v, av => evalAll ps v av
  | .or ps, v, av => evalAny ps v av
  | .not p, v, av => !(evalProp p v av)
  | .tru, _, _ => true
  | .fls, _, _ => false
  | .exactK ps k, v, av =>
    ((ps.filter fun p => evalProp p v av).length) == k
  | .atom i, _, av => av i

def evalAll : List FProp → (Nat → Nat) → (Nat → Bool) → Bool
  | [], _, _ => true
  | p :: ps, v, av => evalProp p v av && evalAll ps v av

def evalAny : List FProp → (Nat → Nat) → (Nat → Bool) → Bool
  | [], _, _ => false
  | p :: ps, v, av => evalProp p v av || evalAny ps v av
end

/-- Node count of a proposition (linear walk; guides the lazy split:
pieces over the threshold stay out of the CNF). -/
def propSize : FProp → Nat
  | .eq _ _ => 1
  | .ne _ _ => 1
  | .distinct ts => 1 + ts.length
  | .lt _ _ => 1
  | .le _ _ => 1
  | .and ps => 1 + (ps.foldl (fun n p => n + propSize p) 0)
  | .or ps => 1 + (ps.foldl (fun n p => n + propSize p) 0)
  | .not p => 1 + propSize p
  | .tru => 1
  | .fls => 1
  | .exactK ps _ => 1 + (ps.foldl (fun n p => n + propSize p) 0)
  | .atom _ => 1

/-- All `(cell, cardinality)` pairs occurring in a proposition
(for one-hot pre-allocation, and for the lazy split's
cell-disjointness test). -/
def collectCells : FProp → List (Nat × Nat)
  | .eq a b => collectTerm a ++ collectTerm b
  | .ne a b => collectTerm a ++ collectTerm b
  | .distinct ts => ts.foldl (fun acc t => collectTerm t ++ acc) []
  | .lt a b => collectTerm a ++ collectTerm b
  | .le a b => collectTerm a ++ collectTerm b
  | .and ps => ps.foldl (fun acc p => collectCells p ++ acc) []
  | .or ps => ps.foldl (fun acc p => collectCells p ++ acc) []
  | .not p => collectCells p
  | .tru => []
  | .fls => []
  | .exactK ps _ => ps.foldl (fun acc p => collectCells p ++ acc) []
  | .atom _ => []
where
  collectTerm : FTerm → List (Nat × Nat)
    | .var c a => [(a, c)]
    | .lit _ _ => []

end Lynth.FinSearch
