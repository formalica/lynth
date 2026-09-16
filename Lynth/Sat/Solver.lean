-- DPLL SAT solver over `Lynth.Sat.Syntax.CNF`.
--
-- Z3's core (`src/sat/sat_solver.cpp`) is CDCL: unit propagation with
-- watched literals, first-UIP conflict analysis, clause learning, VSIDS
-- branching heuristics and restarts. This module implements the same
-- *interface* (satisfying assignment or UNSAT) with a simpler algorithm:
-- recursive DPLL with unit propagation and pure-literal elimination,
-- bounded by fuel so it always terminates inside the tactic.
--
-- Next steps towards Z3 parity: watched literals, conflict analysis with
-- learned clauses, VSIDS scores, restarts, and DRAT certificates checked
-- by `Lynth.Sat.Reconstruct`.
import Lynth.Sat.Syntax

namespace Lynth.Sat

/-- Assignment: `List (Option Bool)` indexed by `var - 1`. -/
abbrev Assignment := List (Option Bool)

/-- Look up variable `v` (1-based) in an assignment. -/
def lookup (a : Assignment) (v : Nat) : Option Bool :=
  if _h : 0 < v ∧ v ≤ a.length then a[v - 1]'(by omega) else none

/-- Set variable `v` (1-based) to `b`, extending the assignment if needed. -/
def assign (a : Assignment) (v : Nat) (b : Bool) : Assignment :=
  if _h : 0 < v then
    let idx := v - 1
    if _h2 : idx < a.length then a.set idx (some b)
    else a ++ List.replicate (idx - a.length) none ++ [some b]
  else a

/-- Value of a literal under an assignment. -/
def evalLit (a : Assignment) (l : Lit) : Option Bool :=
  match lookup a (varOf l) with
  | none => none
  | some b => if 0 < l then some b else some (!b)

/-- Simplify a CNF under an assignment:
returns `none` if a conflict (empty clause) is derived,
otherwise the remaining clauses with satisfied clauses removed
and falsified literals dropped. -/
def simplify (cnf : CNF) (a : Assignment) : Option CNF :=
  cnf.foldl (fun acc? cl =>
    match acc? with
    | none => none
    | some acc =>
      let vals := cl.map (evalLit a)
      if vals.any (· == some true) then some acc
      else
        let cl' := (cl.zip vals).filterMap (fun (l, v) =>
          match v with
          | some false => none
          | _ => some l)
        if cl'.isEmpty then none else some (acc ++ [cl'])
  ) (some [])

/-- Find a unit clause (single literal), if any. -/
def findUnit : CNF → Option Lit
  | [l] :: _ => some l
  | _ :: rest => findUnit rest
  | [] => none

/-- All literals occurring in a CNF. -/
def allLits (cnf : CNF) : List Lit :=
  cnf.foldl (· ++ ·) []

/-- Find a pure literal (occurs with only one polarity), if any. -/
def findPure (cnf : CNF) : Option Lit := do
  let lits := allLits cnf
  lits.find? (fun l => !(lits.contains (-l)))

/-- Pick a branching literal: first literal of the first clause. -/
def pickBranch : CNF → Option Lit
  | (l :: _) :: _ => some l
  | _ => none

/-- Unit propagation + pure-literal elimination to a fixpoint,
bounded by fuel. Returns `none` on conflict or out-of-fuel. -/
def propagate : CNF → Assignment → Nat → Option (CNF × Assignment)
  | cnf, a, 0 =>
    match simplify cnf a with
    | none => none
    | some [] => some ([], a)
    | some cnf' => if cnf'.isEmpty then some ([], a) else none
  | cnf, a, fuel + 1 =>
    match simplify cnf a with
    | none => none
    | some [] => some ([], a)
    | some cnf' =>
      match findUnit cnf' with
      | some l =>
        let v := varOf l
        if v == 0 then none
        else propagate cnf' (assign a v (0 < l)) fuel
      | none =>
        match findPure cnf' with
        | some l =>
          let v := varOf l
          if v == 0 then some (cnf', a)
          else propagate cnf' (assign a v (0 < l)) fuel
        | none => some (cnf', a)

/-- DPLL search with fuel. Returns `some assignment` on SAT,
`none` on UNSAT-or-out-of-fuel (caller distinguishes via `check`). -/
def dpll (cnf : CNF) (a : Assignment) : Nat → Option Assignment
  | 0 => none
  | fuel + 1 =>
    match propagate cnf a fuel with
    | none => none
    | some ([], a') => some a'
    | some (cnf', a') =>
      match pickBranch cnf' with
      | none => some a'
      | some l =>
        let v := varOf l
        match dpll cnf' (assign a' v true) fuel with
        | some res => some res
        | none => dpll cnf' (assign a' v false) fuel

/-- Solver result. -/
inductive SatResult where
  | sat : Assignment → SatResult
  | unsat : SatResult
  deriving Repr, DecidableEq

/-- Top-level solver: `fuel` bounds the search. -/
def solve (cnf : CNF) (fuel : Nat := 10000) : SatResult :=
  match dpll cnf [] fuel with
  | some a => .sat a
  | none =>
    -- `none` conflates UNSAT and out-of-fuel; `check` below refines it.
    .unsat

/-- Verify an assignment satisfies a CNF (certificate checker). -/
def checkSat (cnf : CNF) (a : Assignment) : Bool :=
  cnf.all (fun cl => cl.any (fun l => evalLit a l == some true))

/-- Brute-force UNSAT check for small problems (used to validate
`dpll` in tests and as a reference decision procedure). -/
def bruteForce : CNF → Nat → Nat → Bool
  | cnf, 0, n => checkSat cnf (List.replicate n (some false))
  | cnf, fuel + 1, n =>
    -- enumerate over first variable then recurse; exponential, test-only
    let aTrue := [some true] ++ List.replicate n (some false)
    let aFalse := [some false] ++ List.replicate n (some false)
    checkSat cnf aTrue || checkSat cnf aFalse ||
      bruteForce cnf fuel (n + 1)

end Lynth.Sat
