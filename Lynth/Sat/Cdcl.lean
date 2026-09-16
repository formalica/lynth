-- CDCL SAT solver: conflict-driven clause learning over `Syntax.CNF`.
--
-- Z3's core (`src/sat/sat_solver.cpp`) is CDCL: watched-literal unit
-- propagation, first-UIP conflict analysis, learned clauses, VSIDS
-- branching and restarts. This module upgrades our DPLL (`Solver.lean`,
-- kept as a differential-test reference) with the learning half:
-- reason-tracked propagation, first-UIP resolution, learned clauses and
-- non-chronological backjumping, plus VSIDS activity-based branching.
-- Watched literals and restarts remain TODO (tracked in
-- `docs/Z3-NOTES.md`).
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

/-- First unassigned literal in the first unsatisfied clause.
(Legacy clause-local pick; VSIDS below is the default.) -/
def pickBranch (cnf : CNF) (t : Trail) : Option Lit := do
  for cl in cnf do
    if cl.any fun l => tevalLit t l == some true then pure ()
    else match cl.find? fun l => (tevalLit t l).isNone with
      | some l => return l
      | none => pure ()
  none

/-- VSIDS activities, indexed by `var - 1`. -/
abbrev Activities := Array Nat

/-- Grow activities to cover variable `v`. -/
def growAct (act : Activities) (v : Nat) : Activities :=
  if v ≤ act.size then act
  else act ++ List.replicate (v - act.size) 0

/-- Activity lookup (0 if unseen). -/
def actOf (act : Activities) (v : Nat) : Nat :=
  if h : v - 1 < act.size then act[v - 1]'(by omega) else 0

/-- Bump activities of a learned clause's variables. -/
def bumpAct (act : Activities) (cl : Clause) : Activities :=
  cl.foldl (fun a l =>
    let v := varOf l
    if v == 0 then a
    else
      let a' := growAct a v
      a'.setIfInBounds (v - 1) (actOf a' v + 1)) act

/-- Periodic decay keeps scores bounded (every 64 conflicts, halve). -/
def decayAct (act : Activities) (confTotal : Nat) : Activities :=
  if confTotal % 64 == 63 then act.map (· / 2) else act

/-- VSIDS decision: unassigned variable with maximal activity
(positive polarity). `none` ⟹ every variable assigned. -/
def pickVsids (t : Trail) (act : Activities) (maxV : Nat) : Option Lit := do
  let mut best : Option (Nat × Nat) := none -- (var, activity)
  for v in List.range maxV do
    let w := v + 1
    if (tlookup t w).isNone then
      let a := actOf act w
      match best with
      | none => best := some (w, a)
      | some (_, b) => if b < a then best := some (w, a) else pure ()
  match best with
  | none => none
  | some (w, _) => some (Int.ofNat w)

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

/-- Last-assigned variable among `vars` per `order`. -/
def lastAssigned (vars : List Nat) (order : Order) : Option Nat :=
  order.reverse.find? vars.contains

/-- First-UIP conflict analysis: resolve the conflict clause with reasons
of last-assigned current-level literals until at most one current-level
literal remains. Records the resolution trace alongside. -/
def analyzeT (conflict : Clause) (t : Trail) (ord : Order) (level : Nat)
    (fuel : Nat) : Clause × ResTrace :=
  go conflict [] fuel
where
  go (c : Clause) (tr : ResTrace) : Nat → Clause × ResTrace
    | 0 => (c, tr.reverse)
    | fuel + 1 =>
      let curVars := (c.filter fun l => tlevel t (varOf l) == level).map varOf
      if curVars.length ≤ 1 then (c, tr.reverse)
      else match lastAssigned curVars ord with
        | none => (c, tr.reverse)
        | some v =>
          match c.find? fun l => varOf l == v with
          | none => (c, tr.reverse)
          | some l =>
            match treason t v with
            | none => (c, tr.reverse)
            | some r => go (resolve c r l) ((r, l) :: tr) fuel

/-- First-UIP conflict analysis (trace-discarding wrapper). -/
def analyze (conflict : Clause) (t : Trail) (ord : Order) (level : Nat)
    (fuel : Nat) : Clause :=
  (analyzeT conflict t ord level fuel).1

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
      else go (resolve cur r l) rest

/-- Backjump level: max level in `learnt` excluding the asserting
(current-level) literal. -/
def backjumpLevel (learnt : Clause) (t : Trail) (level : Nat) : Nat :=
  let rest := learnt.filter fun l => tlevel t (varOf l) != level
  rest.foldl (fun m l => Nat.max m (tlevel t (varOf l))) 0

/-- A clause is useless if tautological (`p` and `¬p` both present). -/
def isTaut (cl : Clause) : Bool :=
  cl.any fun l => cl.contains (-l)

/-- Geometric restart limit (MiniSAT-style): `base * 2^min(idx,8)`
conflicts per restart period. -/
def restartLimit (base idx : Nat) : Nat :=
  base * 2 ^ Nat.min idx 8

/-- CDCL driver. Returns `none` on fuel exhaustion (never conflated
with UNSAT). Every learnt clause carries its resolution trace. -/
def cdcl : CNF → Trail → Order → Nat → Nat → Nat → Activities → Nat →
    Nat → Nat → Nat → Nat → List TraceEntry → CdclOut
  | _, _, _, _, _, 0, _, _, _, _, _, _, acc =>
    { result := none, learnt := 0, restarts := 0, traces := acc }
  | cnf, t, ord, level, learnt, fuel + 1, act, confTotal, maxV,
      rIdx, sinceR, rBase, acc =>
    -- restart: keep learnt clauses + activities, erase decisions
    if restartLimit rBase rIdx ≤ sinceR && level != 0 then
      cdcl cnf (eraseAbove t 0) [] 0 learnt fuel act confTotal maxV
        (rIdx + 1) 0 rBase acc
    else match propagateAll cnf t ord level fuel with
    | (.stuck, _, _) =>
      { result := none, learnt, restarts := rIdx, traces := acc }
    | (.conflict c, t1, ord1) =>
      if level == 0 then
        { result := some .unsat, learnt, restarts := rIdx, traces := acc }
      else
        let (learntCl, steps) := analyzeT c t1 ord1 level fuel
        -- Useless learnt clauses are skipped (never re-added); the
        -- backjump below still guarantees progress.
        let useful := !(isTaut learntCl) && !(cnf.contains learntCl)
        let cnf' := if useful then cnf ++ [learntCl] else cnf
        let learnt' := if useful then learnt + 1 else learnt
        let acc' := if useful then acc ++ [(c, steps, learntCl)] else acc
        let unclamped := backjumpLevel learntCl t1 level
        -- Clamp: always erase at least the current decision level, so
        -- every conflict strictly shrinks the trail.
        let blvl := if unclamped < level then unclamped else level - 1
        let t' := eraseAbove t1 blvl
        let ord' := ord1.filter fun v =>
          match tlookup t' v with | some _ => true | none => false
        let act' :=
          if useful then decayAct (bumpAct act learntCl) confTotal else act
        cdcl cnf' t' ord' blvl learnt' fuel
          act' (confTotal + 1) maxV rIdx (sinceR + 1) rBase acc'
    | (.ok, t', ord') =>
      match pickVsids t' act maxV with
      | none =>
        -- no conflict, every variable assigned: model found
        { result := some (.sat (t'.map fun e => e.val)), learnt,
          restarts := rIdx, traces := acc }
      | some l =>
        let v := varOf l
        cdcl cnf (tassign t' v (0 < l) (level + 1) none)
          (ord' ++ [v]) (level + 1) learnt fuel act confTotal maxV
          rIdx sinceR rBase acc

/-- Top-level CDCL solver: result, learned-clause count, restart count,
and resolution traces for every learnt clause. -/
def cdclSolve (cnf : CNF) (fuel : Nat := 10000) (restartBase : Nat := 100) :
    CdclOut :=
  cdcl cnf [] [] 0 0 fuel #[] 0 (numVars cnf) 0 0 restartBase []

end Lynth.Sat.Cdcl
