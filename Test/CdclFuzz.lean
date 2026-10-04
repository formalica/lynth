-- Differential fuzz: CDCL vs DPLL over generated CNFs, models checked.
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

open Lynth.Sat

set_option maxHeartbeats 55 in
/-- Deterministic PRNG (LCG). -/
def cdclFuzz_lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

set_option maxHeartbeats 116 in
/-- Random literal over `nVars` variables, threading the seed. -/
def genLit (s : Nat) (nVars : Nat) : Int × Nat :=
  let s1 := cdclFuzz_lcg s
  let s2 := cdclFuzz_lcg s1
  let v := (s1 % nVars) + 1
  ((if s2 % 2 == 0 then (v : Int) else -(v : Int)), s2)

set_option maxHeartbeats 137 in
/-- Random clause of length `len`. -/
def genClause : Nat → Nat → Nat → List Int × Nat
  | s, 0, _ => ([], s)
  | s, k + 1, nv =>
    let (l, s1) := genLit s nv
    let (rest, s2) := genClause s1 k nv
    (l :: rest, s2)

set_option maxHeartbeats 149 in
/-- Random CNF with fixed clause length. -/
def genCNF : Nat → Nat → Nat → Nat → CNF × Nat
  | s, 0, _, _ => ([], s)
  | s, k + 1, nv, len =>
    let (cl, s1) := genClause s len nv
    let (rest, s2) := genCNF s1 k nv len
    (cl :: rest, s2)

set_option maxHeartbeats 168 in
/-- Random mixed CNF: clause lengths cycle 1..4 (units force the
level-0 init/propagation paths where watch bugs bite). -/
def genMixed : Nat → Nat → Nat → CNF × Nat
  | s, 0, _ => ([], s)
  | s, k + 1, nv =>
    let s1 := cdclFuzz_lcg s
    let len := (s1 % 4) + 1
    let (cl, s2) := genClause s1 len nv
    let (rest, s3) := genMixed s2 k nv
    (cl :: rest, s3)


set_option maxHeartbeats 153 in
/-- Agreement + model check for one seed (small fixed shape). -/
def cdclFuzz_checkSeed (s : Nat) : Bool :=
  let (cnf, _) := genCNF (s + 1) 12 4 3
  match (Cdcl.cdclSolve cnf 10000).result, solve cnf 10000 with
  | some (.sat a), (.sat _) => checkSat cnf a
  | some .unsat, .unsat => true
  | _, _ => false

-- mismatch count over 80 seeds; expect 0
#eval (List.range 80).foldl (fun n s => if cdclFuzz_checkSeed s then n else n + 1) 0

set_option maxHeartbeats 132 in
/-- Agreement + model check for one seed (larger mixed shape with units:
30 clauses over 10 vars, lengths 1..4). -/
def checkSeedBig (s : Nat) : Bool :=
  let (cnf, _) := genMixed (s + 1) 30 10
  match (Cdcl.cdclSolve cnf 20000).result, solve cnf 20000 with
  | some (.sat a), (.sat _) => checkSat cnf a
  | some .unsat, .unsat => true
  | _, _ => false

-- mismatch count over 60 seeds; expect 0
#eval (List.range 60).foldl (fun n s => if checkSeedBig s then n else n + 1) 0

set_option maxHeartbeats 195 in
/-- Every recorded resolution trace validates against the final DB. -/
def checkTraces (s : Nat) : Bool :=
  let (cnf, _) := genCNF (s + 1) 12 4 3
  let o := Cdcl.cdclSolve cnf 10000
  let db := cnf ++ (o.traces.map fun (_, _, learnt) => learnt)
  o.traces.all fun (c, steps, learnt) => Cdcl.checkTrace db c steps learnt

#eval (List.range 80).foldl (fun n s => if checkTraces s then n else n + 1) 0
-- expect 0

set_option maxHeartbeats 160 in
/-- Trace validation on the larger mixed shape. -/
def checkTracesBig (s : Nat) : Bool :=
  let (cnf, _) := genMixed (s + 1) 30 10
  let o := Cdcl.cdclSolve cnf 20000
  let db := cnf ++ (o.traces.map fun (_, _, learnt) => learnt)
  o.traces.all fun (c, steps, learnt) => Cdcl.checkTrace db c steps learnt

#eval (List.range 60).foldl (fun n s => if checkTracesBig s then n else n + 1) 0
-- expect 0

set_option maxHeartbeats 57 in
-- Regression (perf, not correctness): the VMTF init order sorts
-- occurrence-count pairs, and this Sudoku-scale encoder output
-- (25k vars, 85k clauses, ~20k literal occurrences) has thousands of
-- tied keys. A comparator without a tie-breaker drives Lean's
-- `Array.qsort` into pathological partitioning (38s to sort; the whole
-- 9x9 pilot was 49s with 39s spent in `mkWS`). With tie-breaking the
-- same sort is ~0.8s and the pilot is ~8s.
def benchOrder (s : Nat) : Bool :=
  let (cnf, _) := genMixed (s + 1) 30 10
  let _ := Lynth.Sat.Watch.initOrder (cnf.toArray.map (·.toArray)) 10
  true
#eval (List.range 30).foldl (fun n s => if benchOrder s then n else n + 1) 0
-- expect 0
