import Lynth.Sat.Syntax
import Lynth.Sat.Solver

/-!
Watched-literal CDCL core: a native Lean 4 port of CreuSAT's propagation
and decision machinery
([CreuSAT](https://github.com/sarsko/CreuSAT), MIT — MiniSat-style
two-watched-literals with blocking literals and circular search, VMTF
branching, CreuSAT-style phase saving, backjumping to the asserting
level). No FFI: everything here is plain Lean 4 over `Array`s (threaded
linearly so updates stay in place).

Deliberate differences from CreuSAT:
- geometric restarts (kept from our previous engine) instead of EMA;
- fuel-bounded driver (termination by construction, per SPEC);
- first-UIP learning with resolution traces (our `Cdcl` reconstruction
  story: every learnt clause carries a checker-validated derivation);
- a final `checkSat` gate on every SAT answer (defense in depth —
  solver answers become proofs).

Soundness split (unchanged): search untrusted, verdicts proved.
Differential fuzz against `Solver.dpll` must stay at 0 mismatches, and
every emitted trace must validate under `Cdcl.checkTrace`.
-/
namespace Lynth.Sat.Watch

open Lynth.Sat

/-- Watcher: clause reference + blocking literal (CreuSAT `Watcher`). -/
structure Watcher where
  cref : Nat
  blocker : Int
  deriving Inhabited, Repr, DecidableEq, BEq

/-- Clause with circular-search cursor (CreuSAT `Clause.search`). -/
structure WClause where
  lits : Array Int
  search : Nat := 2
  deriving Inhabited, Repr

/-- Solver state. All arrays, threaded linearly for in-place updates.
`assign` uses CreuSAT's phase-saving encoding per variable: `0` false,
`1` true, `2`/`3` unset (saving false/true); unset ⟺ value `≥ 2`. -/
structure WS where
  clauses : Array WClause
  watches : Array (Array Watcher)
  assign : Array Nat
  alevel : Array Nat
  reason : Array (Option Nat)
  tpos : Array Nat
  trail : Array Int
  tlevel : Array Nat
  qhead : Nat
  clevel : Nat
  vnext : Array Nat
  vprev : Array Nat
  vts : Array Nat
  vstart : Nat
  vsearch : Nat
  vtick : Nat
  nvars : Nat
  deriving Inhabited

/-- Watch-list index of a literal (`2*(v-1)` positive, `+1` negative). -/
def widx (l : Int) : Nat :=
  2 * (l.natAbs - 1) + (if 0 < l then 0 else 1)

/-- Value of a literal under the assignment (`none` = unset/invalid). -/
def litVal (s : WS) (l : Int) : Option Bool :=
  let v := l.natAbs
  if v == 0 || s.assign.size ≤ v - 1 then none
  else
    let a := s.assign[v - 1]!
    if 2 ≤ a then none
    else some ((a == 1) == (0 < l))

/-- Is variable `v` (1-based) currently assigned? -/
def isSet (s : WS) (v : Nat) : Bool :=
  v != 0 && v - 1 < s.assign.size && s.assign[v - 1]! < 2

/-- Saved phase of `v` (meaningful even when unset — that is the point). -/
def savedPhase (s : WS) (v : Nat) : Bool :=
  if v == 0 || s.assign.size ≤ v - 1 then false
  else s.assign[v - 1]! % 2 == 1

/-- Literal evaluators. -/
def litSat (s : WS) (l : Int) : Bool :=
  litVal s l == some true
def litUnsat (s : WS) (l : Int) : Bool :=
  litVal s l == some false
def litUnset (s : WS) (l : Int) : Bool :=
  (litVal s l).isNone

/-- Level of an assigned variable (0 for unassigned). -/
def levelOf (s : WS) (v : Nat) : Nat :=
  if isSet s v then s.alevel[v - 1]! else 0

/-- Reason clause (as a `List`, for resolution) of an assigned variable. -/
def reasonOf (s : WS) (v : Nat) : Option Clause :=
  if isSet s v then
    match s.reason[v - 1]! with
    | none => none
    | some c =>
      if c < s.clauses.size then some (s.clauses[c]!.lits.toList)
      else none
  else none

/-- Swap two positions of a clause's literal array. -/
def swapLits (a : Array Int) (i j : Nat) : Array Int :=
  if i < a.size && j < a.size then
    let x := a[i]!
    let y := a[j]!
    (a.setIfInBounds i y).setIfInBounds j x
  else a

/-- Sort by key, breaking ties by variable id. The tie-breaker matters:
occurrence counts have many equal keys, which otherwise make the quicksort
partition badly. This also makes initialization order deterministic. -/
def isortBy (a : Array (Nat × Nat)) : Array (Nat × Nat) :=
  Array.qsort a (fun x y => decide (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)))

/-- Last-assigned variable among `vars` (trail-position order). -/
def lastAssignedW (s : WS) (vars : List Nat) : Option Nat :=
  vars.foldl (fun best v =>
    if !(isSet s v) then best
    else match best with
    | none => some v
    | some b => if s.tpos[b - 1]! < s.tpos[v - 1]! then some v else best) none

/-- Enqueue literal `l` with `reason` at `level`.
Returns `false` on polarity mismatch (impossible by construction at
every call site; the driver treats it as fuel-out, never as UNSAT). -/
def enqLit (s : WS) (l : Int) (reason : Option Nat) (level : Nat) : WS × Bool :=
  let v := l.natAbs
  if v == 0 || s.assign.size ≤ v - 1 then (s, false)
  else if isSet s v then (s, decide (savedPhase s v == (0 < l)))
  else
    let b := if 0 < l then 1 else 0
    let s := { s with assign := s.assign.setIfInBounds (v - 1) b }
    let s := { s with alevel := s.alevel.setIfInBounds (v - 1) level }
    let s := { s with reason := s.reason.setIfInBounds (v - 1) reason }
    let s := { s with tpos := s.tpos.setIfInBounds (v - 1) s.trail.size }
    let s := { s with trail := s.trail.push l }
    let s := { s with tlevel := s.tlevel.push level }
    (s, true)

/-- Pop one trail entry, saving its phase (CreuSAT `backstep`:
`assignments[idx] += 2`). Returns the popped variable. -/
def popTrail (s : WS) : WS × Nat :=
  match s.trail.back? with
  | none => (s, 0)
  | some l =>
    let v := l.natAbs
    let s := { s with trail := s.trail.pop }
    let s := { s with tlevel := s.tlevel.pop }
    let s := { s with assign := if v == 0 || s.assign.size ≤ v - 1 then s.assign else s.assign.setIfInBounds (v - 1) (s.assign[v - 1]! + 2) }
    let s := { s with tpos := if v == 0 || s.tpos.size ≤ v - 1 then s.tpos else s.tpos.setIfInBounds (v - 1) s.nvars }
    (s, v)

/-- Backjump to `blvl`: pop trail entries above it (phases saved),
clamp the propagation queue, resume VMTF search at the most recently
touched variable. -/
def backjump (s : WS) (blvl : Nat) : WS :=
  go s s.nvars 0
where
  go (s : WS) : Nat → Nat → WS
    | 0, best => { s with clevel := blvl, qhead := Nat.min s.qhead s.trail.size, vsearch := if best == s.nvars then s.vsearch else best }
    | n + 1, best =>
      match s.trail.back? with
      | none => { s with clevel := blvl, qhead := Nat.min s.qhead s.trail.size, vsearch := if best == s.nvars then s.vsearch else best }
      | some _ =>
        if s.tlevel.back! ≤ blvl then { s with clevel := blvl, qhead := Nat.min s.qhead s.trail.size, vsearch := if best == s.nvars then s.vsearch else best }
        else
          let (s', v) := popTrail s
          let best' :=
            if v == 0 || s'.vts.size ≤ v - 1 then best
            else if best == s.nvars || s'.vts[best]! < s'.vts[v - 1]! then v - 1
            else best
          go s' n best'

/-- VMTF: unlink `v` (0-based) and push to front with fresh timestamp. -/
def moveToFront (s : WS) (v : Nat) : WS :=
  if v == s.vstart || s.nvars ≤ v then s
  else
    let prev := s.vprev[v]!
    let nxt := s.vnext[v]!
    let s := { s with vnext := s.vnext.setIfInBounds v s.vstart }
    let s := { s with vprev := s.vprev.setIfInBounds v s.nvars }
    let s := { s with vts := s.vts.setIfInBounds v s.vtick }
    let s := { s with vtick := s.vtick + 1 }
    let s := { s with vprev := s.vprev.setIfInBounds s.vstart v }
    let s := { s with vstart := v }
    let s := if prev != s.nvars then
        { s with vnext := s.vnext.setIfInBounds prev nxt } else s
    if nxt != s.nvars then
      { s with vprev := s.vprev.setIfInBounds nxt prev } else s

/-- VMTF conflict bump: sort conflict variables by timestamp, move each
to front (CreuSAT `increment_and_move`). -/
def bumpVmtf (s : WS) (vars : List Nat) : WS :=
  let pairs := vars.toArray.map fun v =>
    (v, if v == 0 || s.vts.size ≤ v - 1 then 0 else s.vts[v - 1]!)
  let sorted := isortBy pairs
  sorted.foldl (fun s (v, _) => if v == 0 then s else moveToFront s (v - 1)) s

/-- VMTF decision: first unset variable from the search cursor
(CreuSAT `get_next`), with full rescan fallback. -/
def getNext (s : WS) : WS × Option Nat :=
  go s s.vsearch (s.nvars + 1)
where
  go (s : WS) (cur fuel : Nat) : WS × Option Nat :=
    match fuel with
    | 0 => (s, fullScan s)
    | f + 1 =>
      if cur == s.nvars then (s, fullScan s)
      else if cur < s.assign.size && !(isSet s (cur + 1)) then
        let nxt := if cur < s.vnext.size then s.vnext[cur]! else s.nvars
        ({ s with vsearch := nxt }, some cur)
      else
        let nxt := if cur < s.vnext.size then s.vnext[cur]! else s.nvars
        go s nxt f
  fullScan (s : WS) : Option Nat :=
    (List.range s.nvars).find? fun i => !(isSet s (i + 1))

/-- Scan clause positions `[k, upto)` for the first non-false literal. -/
def scanGo (s : WS) (c : WClause) (k upto : Nat) : Option Nat :=
  if upto ≤ k then none
  else if k < c.lits.size && !(litUnsat s c.lits[k]!) then some k
  else scanGo s c (k + 1) upto
termination_by upto - k

/-- Visit one watcher of the newly-false literal `p`
(CreuSAT `propagate_lit_with_regard_to_clause`): blocker fast-path,
watched-pair SAT check, circular search for a replacement watch
(swapped into position 0, watcher re-homed — `stay`), else unit
propagation or conflict. -/
inductive VisitRes where
  | adv
  | stay
  | conflict (cref : Nat)
  deriving DecidableEq

def visitWatch (s : WS) (p : Int) (j : Nat) : WS × VisitRes :=
  let wi := widx p
  let w := s.watches[wi]![j]!
  if litSat s w.blocker then (s, .adv)
  else
    let c := s.clauses[w.cref]!
    let l0 := c.lits[0]!
    let l1 := c.lits[1]!
    -- NOTE: blockers are read-only cache here. Updating them (as
    -- CreuSAT does in Rust) costs an `O(len)` persistent-array copy
    -- per visit in Lean and pessimize the hot path; stale blockers
    -- stay sound (a miss just falls through to the watched pair).
    if litSat s l0 then (s, .adv)
    else if litSat s l1 then (s, .adv)
    else match findNewWatch s w.cref p with
      | (s', some _) =>
        -- re-home the watcher under the new watched literal (at [0])
        let newLit := s'.clauses[w.cref]!.lits[0]!
        let wl := s'.watches[wi]!
        let wl' := (wl.setIfInBounds j wl.back!).pop
        let nl := s'.watches.getD (widx (-newLit)) #[]
        let w' := (s'.watches.setIfInBounds wi wl').setIfInBounds (widx (-newLit)) (nl.push w)
        ({ s' with watches := w' }, .stay)
      | (s', none) =>
        let c' := s'.clauses[w.cref]!
        let a0 := c'.lits[0]!
        let b1 := c'.lits[1]!
        if litUnset s' a0 then
          if litUnset s' b1 then (s', .adv)
          else
            -- unit: propagate `a0`
            match enqLit s' a0 (some w.cref) s'.clevel with
            | (s'', true) => (s'', .adv)
            | (s'', false) => (s'', .conflict w.cref)
        else if litUnset s' b1 then
          -- unit: swap to position 0 (convention) and propagate
          let c'' : WClause := { lits := swapLits c'.lits 0 1, search := c'.search }
          let s'' := { s' with clauses := s'.clauses.setIfInBounds w.cref c'' }
          match enqLit s'' b1 (some w.cref) s''.clevel with
          | (s''', true) => (s''', .adv)
          | (s''', false) => (s''', .conflict w.cref)
        else (s', .conflict w.cref)
where
  /-- Circular search for a non-false literal at/after the cursor
  (CreuSAT `exists_new_watchable_lit`): scan `[cursor, len)` then
  `[2, cursor)`; the winner is swapped into the watched pair with the
  new watch at position 0. -/
  findNewWatch (s : WS) (cref : Nat) (p : Int) : WS × Option Nat :=
    let c := s.clauses[cref]!
    let n := c.lits.size
    let cur := Nat.max (Nat.min c.search n) 2
    match scanGo s c cur n with
    | some k => (moveWatch s cref p k, some k)
    | none =>
      match scanGo s c 2 cur with
      | some k => (moveWatch s cref p k, some k)
      | none => (s, none)
  /-- Swap winner `k` into the watched pair, new watch at position 0.
  The currently-false watched literal is `¬p` (same var as `p`):
  if it sits at 0, one swap; else rotate through 1. -/
  moveWatch (s : WS) (cref : Nat) (p : Int) (k : Nat) : WS :=
    let c := s.clauses[cref]!
    let lits :=
      if c.lits[0]!.natAbs == p.natAbs then swapLits c.lits k 0
      else swapLits (swapLits c.lits k 1) 1 0
    { s with clauses := s.clauses.setIfInBounds cref { lits := lits, search := k } }

/-- Propagation outcome. `stuck` means fuel ran out with units
possibly pending (must not be read as a model). -/
inductive POut where
  | ok
  | conflict (cref : Nat)
  | stuck

/-- Process all watchers of newly-assigned literal `p`
(CreuSAT `propagate_literal`). -/
def propLit (s : WS) (p : Int) : Nat → Nat → WS × POut × Nat
  | _, 0 => (s, .stuck, 0)
  | j, f + 1 =>
    let wl := s.watches.getD (widx p) #[]
    if j < wl.size then
      match visitWatch s p j with
      | (s', .adv) => propLit s' p (j + 1) f
      | (s', .stay) => propLit s' p j f
      | (s', .conflict c) => (s', .conflict c, f)
    else (s, .ok, f)

/-- Drain the propagation queue (CreuSAT `unit_propagate`). -/
def propLoop (s : WS) : Nat → WS × POut × Nat
  | 0 => (s, .stuck, 0)
  | f + 1 =>
    if s.qhead < s.trail.size then
      let p := s.trail[s.qhead]!
      let s := { s with qhead := s.qhead + 1 }
      match propLit s p 0 f with
      | (s', .ok, _) => propLoop s' f
      | (s', .conflict c, _) => (s', .conflict c, f)
      | (s', .stuck, _) => (s', .stuck, 0)
    else (s, .ok, f)

/-- VMTF occurrence-count init order (descending). -/
def initOrder (cls : Array (Array Int)) (nvars : Nat) : Array Nat :=
  let counts := cls.foldl (fun acc cl =>
    cl.foldl (fun acc l =>
      let v := l.natAbs
      if v == 0 || nvars < v then acc
      else acc.setIfInBounds (v - 1) (acc[v - 1]! + 1))
      acc) (Array.replicate nvars 0)
  let pairs : Array (Nat × Nat) :=
    (List.range nvars).toArray.map fun i => (counts[i]!, i)
  (isortBy pairs |>.reverse).map (·.2)

/-- Build the initial state; `none` = immediate UNSAT (empty clause or
opposing units). Unit clauses are enqueued at level 0. -/
def mkWS (cnf : CNF) : Option WS := do
  -- sanitize: drop `0` literals (parity with the old engine, where a
  -- lone `0` forced conflict and elsewhere it stayed unset forever)
  let cls : Array (Array Int) :=
    (cnf.map fun cl => ((cl.filter (· != 0)).toArray)).toArray
  if cls.any (·.isEmpty) then none
  else
    let nvars := numVars cnf
    let mut clauses : Array WClause := #[]
    for cl in cls do
      clauses := clauses.push { lits := cl, search := 2 }
    let mut watches : Array (Array Watcher) :=
      Array.replicate (2 * nvars) #[]
    for cref in List.range clauses.size do
      let c := clauses[cref]!
      if 1 < c.lits.size then
        let l0 := c.lits[0]!
        let l1 := c.lits[1]!
        watches := watches.setIfInBounds (widx (-l0))
          ((watches.getD (widx (-l0)) #[]).push { cref, blocker := l1 })
        watches := watches.setIfInBounds (widx (-l1))
          ((watches.getD (widx (-l1)) #[]).push { cref, blocker := l0 })
    let order := initOrder (clauses.map (·.lits)) nvars
    let mut vnext := Array.replicate nvars nvars
    let mut vprev := Array.replicate nvars nvars
    let mut vts := Array.replicate nvars 0
    for rank in List.range order.size do
      let v := order[rank]!
      vts := vts.setIfInBounds v (nvars - rank)
      vprev := vprev.setIfInBounds v
        (if rank == 0 then nvars else order[rank - 1]!)
      vnext := vnext.setIfInBounds v
        (if rank + 1 < order.size then order[rank + 1]! else nvars)
    let vstart := if order.isEmpty then nvars else order[0]!
    let mut s : WS :=
      { clauses := clauses, watches := watches, assign := Array.replicate nvars 2, alevel := Array.replicate nvars 0, reason := Array.replicate nvars none, tpos := Array.replicate nvars nvars, trail := #[], tlevel := #[], qhead := 0, clevel := 0, vnext := vnext, vprev := vprev, vts := vts, vstart := vstart, vsearch := vstart, vtick := nvars + 1, nvars := nvars }
    -- enqueue unit clauses at level 0
    match enqUnits s (List.range clauses.size) with
    | none => none
    | some s' => some s'
where
  enqUnits (s : WS) : List Nat → Option WS
    | [] => some s
    | cref :: rest =>
      let c := s.clauses[cref]!
      if c.lits.size != 1 then enqUnits s rest
      else match enqLit s c.lits[0]! (some cref) 0 with
        | (s', true) => enqUnits s' rest
        | (_, false) => none

/-- Resolve `c` (∋ `l`) with reason `r` (∋ `¬l`) on `l`. -/
def wresolve (c r : Clause) (l : Lit) : Clause :=
  let c' := c.filter (· != l)
  let r' := r.filter (· != -l)
  c' ++ r'.filter fun m => !(c'.contains m)

/-- First-UIP conflict analysis over array state (same algorithm as the
old `analyzeT`, same trace format). -/
def analyzeW (s : WS) (conflict : Clause) (level fuel : Nat) :
    Clause × List (Clause × Lit) :=
  go conflict [] fuel
where
  go (c : Clause) (tr : List (Clause × Lit)) : Nat → Clause × List (Clause × Lit)
    | 0 => (c, tr.reverse)
    | f + 1 =>
      let curVars := (c.filter fun l => levelOf s (varOf l) == level).map varOf
      if curVars.length ≤ 1 then (c, tr.reverse)
      else match lastAssignedW s curVars with
        | none => (c, tr.reverse)
        | some v =>
          match c.find? fun l => varOf l == v with
          | none => (c, tr.reverse)
          | some l =>
            match reasonOf s v with
            | none => (c, tr.reverse)
            | some r => go (wresolve c r l) ((r, l) :: tr) f

/-- Backjump level: max level in `learnt` excluding the asserting
(current-level) literal. -/
def backjumpLevelW (s : WS) (learnt : Clause) (level : Nat) : Nat :=
  let rest := learnt.filter fun l => levelOf s (varOf l) != level
  rest.foldl (fun m l => Nat.max m (levelOf s (varOf l))) 0

/-- A clause is useless if tautological. -/
def isTautW (cl : Clause) : Bool :=
  cl.any fun l => cl.contains (-l)

/-- Geometric restart limit (kept from the previous engine). -/
def restartLimitW (base idx : Nat) : Nat :=
  base * 2 ^ Nat.min idx 8

/-- Driver output (mirrors `CdclOut`; packed by `Cdcl.cdclSolve`). -/
structure WOut where
  result : Option SatResult
  learnt : Nat
  restarts : Nat
  traces : List (Clause × List (Clause × Lit) × Clause)
  deriving Repr

/-- CDCL driver: propagate → analyze/learn/backjump → decide, fueled. -/
def wcdcl (s : WS) (fuel learnt confTotal rIdx sinceR rBase : Nat)
    (acc : List (Clause × List (Clause × Lit) × Clause)) : WOut :=
  match fuel with
  | 0 => { result := none, learnt, restarts := rIdx, traces := acc }
  | f + 1 =>
    if restartLimitW rBase rIdx ≤ sinceR && s.clevel != 0 then
      let s' := backjump s 0
      wcdcl s' f learnt confTotal (rIdx + 1) 0 rBase acc
    else match propLoop s f with
      | (_s', .stuck, _) =>
        { result := none, learnt, restarts := rIdx, traces := acc }
      | (s', .conflict c, _) =>
        if s'.clevel == 0 then
          { result := some .unsat, learnt, restarts := rIdx, traces := acc }
        else
          let conflict := s'.clauses[c]!.lits.toList
          let (learntCl, steps) := analyzeW s' conflict s'.clevel f
          if learntCl.isEmpty then
            -- empty resolvent = genuine contradiction
            { result := some .unsat, learnt, restarts := rIdx, traces := acc }
          else if isTautW learntCl then
            let s'' := bumpVmtf s' (conflict.map varOf)
            let blvl := Nat.min (backjumpLevelW s'' learntCl s''.clevel) (s''.clevel - 1)
            wcdcl (backjump s'' blvl) f learnt (confTotal + 1)
              rIdx (sinceR + 1) rBase acc
          else
            let nc := s'.clauses.size
            let arr := learntCl.toArray
            let s'' := { s' with clauses := s'.clauses.push { lits := arr, search := 2 } }
            let s'' := bumpVmtf s'' (learntCl.map varOf)
            -- watch the first two literals (unit clause: no watchers)
            let s'' := match arr[0]?, arr[1]? with
              | some l0, some l1 =>
                let w0 := s''.watches.getD (widx (-l0)) #[]
                let w1 := s''.watches.getD (widx (-l1)) #[]
                let w' := (s''.watches.setIfInBounds (widx (-l0)) (w0.push { cref := nc, blocker := l1 })).setIfInBounds (widx (-l1)) (w1.push { cref := nc, blocker := l0 })
                { s'' with watches := w' }
              | _, _ => s''
            let blvl := Nat.min (backjumpLevelW s'' learntCl s''.clevel) (s''.clevel - 1)
            -- asserting literal: the (unique) current-level literal,
            -- identified BEFORE backjump erases levels
            let asrt := learntCl.find? fun l =>
              levelOf s'' (varOf l) == s''.clevel
            let s3 := backjump s'' blvl
            -- enqueue it (unset by construction: its level exceeds
            -- `blvl`); skip defensively if assigned (progress still
            -- holds: the falsified learnt re-conflicts lower)
            let s3 := match asrt with
              | some l =>
                if litUnset s3 l then (enqLit s3 l (some nc) s3.clevel).1
                else s3
              | none => s3
            wcdcl s3 f (learnt + 1) (confTotal + 1)
              rIdx (sinceR + 1) rBase (acc ++ [(conflict, steps, learntCl)])
      | (s', .ok, _) =>
        match getNext s' with
        | (s'', none) =>
          -- all assigned, no conflict: every clause satisfied
          let model := (List.range s''.nvars).map fun i =>
            let a := s''.assign[i]!
            if a < 2 then some (a == 1) else none
          { result := some (.sat model), learnt := learnt, restarts := rIdx, traces := acc }
        | (s'', some v) =>
          let pol := savedPhase s'' (v + 1)
          let lit := if pol then Int.ofNat (v + 1) else -Int.ofNat (v + 1)
          let (s3, ok) := enqLit s'' lit none (s''.clevel + 1)
          if !ok then
            { result := none, learnt, restarts := rIdx, traces := acc }
          else
            wcdcl { s3 with clevel := s3.clevel + 1 } f learnt confTotal
              rIdx sinceR rBase acc

/-- Top-level watched-literal solver over array state. -/
def wsolve (s : WS) (fuel restartBase : Nat) : WOut :=
  wcdcl s fuel 0 0 0 0 restartBase []

end Lynth.Sat.Watch
