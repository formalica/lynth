-- Propositional skeleton + Tseitin encoding into `Lynth.Sat.Syntax.CNF`.
--
-- `PropForm` is the SAT procedure's internal language for the propositional
-- skeleton of a Lean goal (cf. Z3's `src/sat` boolean core, which likewise
-- sees only the boolean structure while theories handle atoms). Tseitin
-- encoding keeps CNF conversion linear; validity of `f` is reduced to
-- UNSAT of `¬f`, exactly like a Z3 `check` on the negated goal.
import Lynth.Sat.Syntax
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

namespace Lynth.Sat.Encode

/-- Propositional skeleton with `Nat`-indexed opaque atoms. -/
inductive PropForm where
  | atom : Nat → PropForm
  | tru : PropForm
  | fls : PropForm
  | neg : PropForm → PropForm
  | conj : PropForm → PropForm → PropForm
  | disj : PropForm → PropForm → PropForm
  | imp : PropForm → PropForm → PropForm
  deriving Repr, DecidableEq

/-- Tseitin state: next fresh variable (atoms occupy `1 .. nAtoms`). -/
abbrev TseitinM := StateM Nat

/-- Fresh variable. -/
def fresh : TseitinM Nat := do
  let n ← get
  set (n + 1)
  pure n

/-- Tseitin transform: returns the literal representing `f` plus
defining clauses. Atom `i` maps to variable `i + 1`. -/
def tseitin : PropForm → TseitinM (Lit × CNF)
  | .atom i => pure (Int.ofNat (i + 1), [])
  | .tru => do
    let v ← fresh
    pure (Int.ofNat v, [[Int.ofNat v]])
  | .fls => do
    let v ← fresh
    pure (Int.ofNat v, [[-Int.ofNat v]])
  | .neg f => do
    let (a, c) ← tseitin f
    let v ← fresh
    let V := Int.ofNat v
    pure (V, c ++ [[-V, -a], [V, a]])
  | .conj a b => do
    let (la, ca) ← tseitin a
    let (lb, cb) ← tseitin b
    let v ← fresh
    let V := Int.ofNat v
    pure (V, ca ++ cb ++ [[-V, la], [-V, lb], [V, -la, -lb]])
  | .disj a b => do
    let (la, ca) ← tseitin a
    let (lb, cb) ← tseitin b
    let v ← fresh
    let V := Int.ofNat v
    pure (V, ca ++ cb ++ [[-la, V], [-lb, V], [-V, la, lb]])
  | .imp a b => do
    -- v ↔ (¬a ∨ b): (¬v ∨ ¬a ∨ b), (a ∨ v), (¬b ∨ v)
    let (la, ca) ← tseitin a
    let (lb, cb) ← tseitin b
    let v ← fresh
    let V := Int.ofNat v
    pure (V, ca ++ cb ++ [[-V, -la, lb], [la, V], [-lb, V]])

/-- Encode validity check of `f` with `nAtoms` atoms: CNF for `¬f`.
UNSAT ⟹ `f` is a propositional tautology. -/
def encodeNeg (f : PropForm) (nAtoms : Nat) : CNF :=
  let ((top, cls), _) := StateT.run (tseitin (.neg f)) (nAtoms + 1)
  cls ++ [[top]]

/-- Validity oracle: `true` if the skeleton is a tautology
(CDCL proves UNSAT of the negation within `fuel`).
`none` (out of fuel) reads as `false`: inconclusive, never a
false-positive. -/
def isTautology (f : PropForm) (nAtoms : Nat) (fuel : Nat := 10000) : Bool :=
  match Cdcl.cdclSolve (encodeNeg f nAtoms) fuel with
  | (some .unsat, _) => true
  | _ => false

end Lynth.Sat.Encode
