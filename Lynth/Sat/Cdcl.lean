import Lynth.Sat.Syntax
import Lynth.Sat.Solver
import Lynth.Sat.Watch

/-!
CDCL SAT solver: conflict-driven clause learning over `Syntax.CNF`.

Z3's core (`src/sat/sat_solver.cpp`) is CDCL: watched-literal unit
propagation, first-UIP conflict analysis, learned clauses, VSIDS
branching and restarts. Our engine (`Watch.lean`, a native Lean 4 port
of CreuSAT's propagation and decision machinery) provides MiniSat-style
two-watched-literals with blocking literals and circular search, VMTF
branching, phase saving, and backjumping; this module keeps the
reconstruction story (first-UIP resolution traces + independent
checker) and the top-level `cdclSolve` entry point with identical
semantics. The DPLL reference (`Solver.lean`) stays as the differential
oracle: any engine disagreement shows up as fuzz mismatch.
-/
namespace Lynth.Sat.Cdcl

open Lynth.Sat

/-- A resolution step: resolve `current` (∋ `pivot`) with `reason`
(∋ `¬pivot`). The resolvent is recomputed by the checker. -/
abbrev ResStep := Clause × Lit

/-- Resolution trace: the conflict clause plus derivation steps. -/
abbrev ResTrace := List ResStep

/-- A validated learning event: conflict, steps, and final learnt clause. -/
abbrev TraceEntry := Clause × ResTrace × Clause

/-- CDCL output bundle. -/
structure CdclOut where
  result : Option SatResult
  learnt : Nat
  restarts : Nat
  traces : List TraceEntry
  deriving Repr

/-- Independent trace checker: replay the derivation, verifying every
parent against the clause database. -/
def checkTrace (db : CNF) (conflict : Clause) (steps : ResTrace)
    (learnt : Clause) : Bool :=
  if !(db.contains conflict) then false
  else match go conflict steps with
    | some final => final == learnt
    | none => false
where
  go : Clause → ResTrace → Option Clause
    | cur, [] => some cur
    | cur, (r, l) :: rest =>
      if !(db.contains r) then none
      else if !(cur.contains l) then none
      else if !(r.contains (-l)) then none
      else go (Watch.wresolve cur r l) rest

/-- Top-level CDCL solver: result, learned-clause count, restart count,
and resolution traces for every learnt clause. Duplicate literals are
stripped up front: they defeat unit detection (e.g. `xor(v,v)` would
otherwise emit `[-o,-v,-v]` and stall learning).
SAT answers pass a final `checkSat` gate (defense in depth: a model
that fails the gate is reported as unknown, never as SAT).
`branch` (default empty = all vars) restricts branching to the
given SAT variables (the grid cells' one-hot bits); other callers
keep the default. -/
def cdclSolve (cnf : CNF) (fuel : Nat := 10000) (restartBase : Nat := 100)
    (branch : Std.HashSet Nat := ∅) : CdclOut :=
  let cnf := cnf.map (·.eraseDups)
  match Watch.mkWS cnf branch with
  | none =>
    { result := some .unsat, learnt := 0, restarts := 0, traces := [] }
  | some s =>
    let o := Watch.wsolve s fuel restartBase
    let result := match o.result with
      | some (.sat m) =>
        if checkSat cnf m then some (.sat m) else none
      | r => r
    { result, learnt := o.learnt, restarts := o.restarts, traces := o.traces }

end Lynth.Sat.Cdcl
