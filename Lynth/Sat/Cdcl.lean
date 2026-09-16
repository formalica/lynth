-- CDCL SAT solver: conflict-driven clause learning over `Syntax.CNF`.
--
-- Z3's core (`src/sat/sat_solver.cpp`) is CDCL: watched-literal unit
-- propagation, first-UIP conflict analysis, learned clauses, VSIDS
-- branching and restarts. This module upgrades our DPLL (`Solver.lean`,
-- kept as a differential-test reference) with the learning half:
-- reason-tracked propagation, first-UIP resolution, learned clauses and
-- non-chronological backjumping. Watched literals, VSIDS and restarts
-- remain TODO (tracked in `docs/Z3-NOTES.md`).
import Lynth.Sat.Syntax
import Lynth.Sat.Solver

namespace Lynth.Sat.Cdcl

/-- Trail entry: value, decision level, and forcing clause (`none` for
decisions). -/
structure TEntry where
  val : Option Bool := none
  level : Nat := 0
  reason : Option Clause := none
  deriving Repr, DecidableEq, Inhabited

/-- Assignment trail, indexed by `var - 1`. -/
abbrev Trail := List TEntry

/-- Assignment order (variables in assignment sequence, for UIP search). -/
abbrev Order := List Nat

open Lynth.Sat

/-- Value lookup. -/
def tlookup (t : Trail) (v : Nat) : Option Bool :=
  if h : 0 < v ∧ v ≤ t.length then
    match t[v - 1]'(by omega) with
    | { val, .. } => val
  else none

/-- Level lookup (0 for unassigned). -/
def tlevel (t : Trail) (v : Nat) : Nat :=
  if h : 0 < v ∧ v ≤ t.length then
    match t[v - 1]'(by omega) with
    | { level, .. } => level
  else 0

/-- Reason lookup. -/
def treason (t : Trail) (v : Nat) : Option Clause :=
  if h : 0 < v ∧ v ≤ t.length then
    match t[v - 1]'(by omega) with
    | { reason, .. } => reason
  else none

/-- Assign `v := b` at `level` with `reason`, extending the trail. -/
def tassign (t : Trail) (v : Nat) (b : Bool) (level : Nat)
    (reason : Option Clause) : Trail :=
  if _h : 0 < v then
    let idx := v - 1
    let e : TEntry := { val := some b, level, reason }
    if _h2 : idx < t.length then t.set idx e
    else t ++ List.replicate (idx - t.length) (default : TEntry) ++ [e]
  else t

/-- Erase assignments above `blvl` (backjump). -/
def eraseAbove (t : Trail) (blvl : Nat) : Trail :=
  t.map fun e => if blvl < e.level then (default : TEntry) else e

/-- Value of a literal under a trail. -/
def tevalLit (t : Trail) (l : Lit) : Option Bool :=
  match tlookup t (varOf l) with
  | none => none
  | some b => if 0 < l then some b else some (!b)

/-- First clause all of whose literals are false (conflict), if any. -/
def findConflict (cnf : CNF) (t : Trail) : Option Clause :=
  cnf.find? fun cl => cl.all fun l => tevalLit t l == some false

/-- A unit consequence: clause with exactly one non-false literal, which
is unassigned. Returns the literal + forcing clause. -/
def findUnit (cnf : CNF) (t : Trail) : Option (Lit × Clause) := do
  for cl in cnf do
    let rest := cl.filter fun l => tevalLit t l != some false
    match rest with
    | [l] => if (tevalLit t l).isNone then return (l, cl) else pure ()
    | _ => pure ()
  none

/-- First unassigned literal in the first unsatisfied clause. -/
def pickBranch (cnf : CNF) (t : Trail) : Option Lit := do
  for cl in cnf do
    if cl.any fun l => tevalLit t l == some true then pure ()
    else match cl.find? fun l => (tevalLit t l).isNone with
      | some l => return l
      | none => pure ()
  none

/-- Propagation outcome. `stuck` means fuel ran out with unit
consequences still pending (must not be read as a model). -/
inductive PropOut where
  | conflict : Clause → PropOut
  | ok : PropOut
  | stuck : PropOut

/-- Exhaustive unit propagation at `level`, fuel-bounded. -/
def propagateAll (cnf : CNF) : Trail → Order → Nat → Nat →
    (PropOut × Trail × Order)
  | t, ord, _, 0 =>
    match findConflict cnf t with
    | some c => (.conflict c, t, ord)
    | none =>
      match findUnit cnf t with
      | some _ => (.stuck, t, ord)
      | none => (.ok, t, ord)
  | t, ord, level, fuel + 1 =>
    match findConflict cnf t with
    | some c => (.conflict c, t, ord)
    | none =>
      match findUnit cnf t with
      | none => (.ok, t, ord)
      | some (l, c) =>
        let v := varOf l
        if v == 0 then (.conflict c, t, ord)
        else propagateAll cnf (tassign t v (0 < l) level (some c))
          (ord ++ [v]) level fuel

/-- Resolve `c` (∋ `l`) with reason `r` (∋ `¬l`) on `l`. -/
def resolve (c r : Clause) (l : Lit) : Clause :=
  let c' := c.filter (· != l)
  let r' := r.filter (· != -l)
  c' ++ r'.filter fun m => !(c'.contains m)

/-- Last-assigned variable among `vars` per `order`. -/
def lastAssigned (vars : List Nat) (order : Order) : Option Nat :=
  order.reverse.find? vars.contains

/-- First-UIP conflict analysis: resolve the conflict clause with reasons
of last-assigned current-level literals until at most one current-level
literal remains. -/
def analyze (conflict : Clause) (t : Trail) (ord : Order) (level : Nat)
    (fuel : Nat) : Clause :=
  match fuel with
  | 0 => conflict
  | fuel + 1 =>
    let curVars := (conflict.filter fun l => tlevel t (varOf l) == level).map varOf
    if curVars.length ≤ 1 then conflict
    else match lastAssigned curVars ord with
      | none => conflict
      | some v =>
        -- find the literal of `v` in the clause
        match conflict.find? fun l => varOf l == v with
        | none => conflict
        | some l =>
          match treason t v with
          | none => conflict -- decision literal: cannot resolve further
          | some r => analyze (resolve conflict r l) t ord level fuel

/-- Backjump level: max level in `learnt` excluding the asserting
(current-level) literal. -/
def backjumpLevel (learnt : Clause) (t : Trail) (level : Nat) : Nat :=
  let rest := learnt.filter fun l => tlevel t (varOf l) != level
  rest.foldl (fun m l => Nat.max m (tlevel t (varOf l))) 0

/-- CDCL driver. Returns `none` on fuel exhaustion (never conflated
with UNSAT), plus the number of learned clauses. -/
def cdcl : CNF → Trail → Order → Nat → Nat → Nat →
    (Option SatResult × Nat)
  | _, _, _, _, learnt, 0 => (none, learnt)
  | cnf, t, ord, level, learnt, fuel + 1 =>
    match propagateAll cnf t ord level fuel with
    | (.stuck, _, _) => (none, learnt)
    | (.conflict c, t1, ord1) =>
      if level == 0 then (some .unsat, learnt)
      else
        let learntCl := analyze c t1 ord1 level fuel
        let blvl := backjumpLevel learntCl t1 level
        let t' := eraseAbove t1 blvl
        let ord' := ord1.filter fun v =>
          match tlookup t' v with | some _ => true | none => false
        cdcl (cnf ++ [learntCl]) t' ord' blvl (learnt + 1) fuel
    | (.ok, t', ord') =>
      match pickBranch cnf t' with
      | none =>
        -- no conflict, nothing left to decide: model found
        (some (.sat (t'.map fun e => e.val)), learnt)
      | some l =>
        let v := varOf l
        cdcl cnf (tassign t' v (0 < l) (level + 1) none)
          (ord' ++ [v]) (level + 1) learnt fuel

/-- Top-level CDCL solver: result plus learned-clause count. -/
def cdclSolve (cnf : CNF) (fuel : Nat := 10000) : Option SatResult × Nat :=
  cdcl cnf [] [] 0 0 fuel

end Lynth.Sat.Cdcl
