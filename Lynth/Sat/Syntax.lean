-- Internal SAT representation for `Lynth.Sat`.
-- Mirrors the role of Z3's `src/sat` core: clauses over boolean literals,
-- but kept minimal (DPLL over DIMACS-style `List (List Int)`).
-- Z3 uses CDCL with clause learning, VSIDS branching, restarts and DRAT
-- proofs (`sat_solver.cpp`, `sat_drat.cpp`); we start with DPLL + unit
-- propagation and grow towards clause learning (see docs/Z3-NOTES.md).
namespace Lynth.Sat

/-- A literal: nonzero `Int`. `n > 0` means variable `n` is true,
`n < 0` means variable `n` is false. `0` is never a valid literal. -/
abbrev Lit := Int

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Lit

/-- CNF is a conjunction of clauses. Empty CNF = `True`,
CNF containing `[]` = `False`. -/
abbrev CNF := List Clause

/-- Variable of a literal (absolute value as `Nat`). -/
def varOf : Lit → Nat
  | n => n.natAbs

/-- Number of distinct variables in a CNF. -/
def numVars (cnf : CNF) : Nat :=
  cnf.foldl (fun acc cl => cl.foldl (fun acc lit => Nat.max acc (varOf lit)) acc) 0

/-- Negation of a literal. -/
def negLit : Lit → Lit
  | n => -n

end Lynth.Sat
