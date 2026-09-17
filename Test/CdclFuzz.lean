-- Differential fuzz: CDCL vs DPLL over generated CNFs, models checked.
import Lynth.Sat.Solver
import Lynth.Sat.Cdcl

open Lynth.Sat

/-- Deterministic PRNG (LCG). -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

/-- Random literal over `nVars` variables, threading the seed. -/
def genLit (s : Nat) (nVars : Nat) : Int × Nat :=
  let s1 := lcg s
  let s2 := lcg s1
  let v := (s1 % nVars) + 1
  ((if s2 % 2 == 0 then (v : Int) else -(v : Int)), s2)

/-- Random clause of length `len`. -/
def genClause : Nat → Nat → Nat → List Int × Nat
  | s, 0, _ => ([], s)
  | s, k + 1, nv =>
    let (l, s1) := genLit s nv
    let (rest, s2) := genClause s1 k nv
    (l :: rest, s2)

/-- Random CNF with fixed clause length. -/
def genCNF : Nat → Nat → Nat → Nat → CNF × Nat
  | s, 0, _, _ => ([], s)
  | s, k + 1, nv, len =>
    let (cl, s1) := genClause s len nv
    let (rest, s2) := genCNF s1 k nv len
    (cl :: rest, s2)

/-- Random mixed CNF: clause lengths cycle 1..4 (units force the
level-0 init/propagation paths where watch bugs bite). -/
def genMixed : Nat → Nat → Nat → CNF × Nat
  | s, 0, _ => ([], s)
  | s, k + 1, nv =>
    let s1 := lcg s
    let len := (s1 % 4) + 1
    let (cl, s2) := genClause s1 len nv
    let (rest, s3) := genMixed s2 k nv
    (cl :: rest, s3)


/-- Agreement + model check for one seed (small fixed shape). -/
def checkSeed (s : Nat) : Bool :=
  let (cnf, _) := genCNF (s + 1) 12 4 3
  match (Cdcl.cdclSolve cnf 10000).result, solve cnf 10000 with
  | some (.sat a), (.sat _) => checkSat cnf a
  | some .unsat, .unsat => true
  | _, _ => false

-- mismatch count over 80 seeds; expect 0
#eval (List.range 80).foldl (fun n s => if checkSeed s then n else n + 1) 0

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

/-- Every recorded resolution trace validates against the final DB. -/
def checkTraces (s : Nat) : Bool :=
  let (cnf, _) := genCNF (s + 1) 12 4 3
  let o := Cdcl.cdclSolve cnf 10000
  let db := cnf ++ (o.traces.map fun (_, _, learnt) => learnt)
  o.traces.all fun (c, steps, learnt) => Cdcl.checkTrace db c steps learnt

#eval (List.range 80).foldl (fun n s => if checkTraces s then n else n + 1) 0
-- expect 0

/-- Trace validation on the larger mixed shape. -/
def checkTracesBig (s : Nat) : Bool :=
  let (cnf, _) := genMixed (s + 1) 30 10
  let o := Cdcl.cdclSolve cnf 20000
  let db := cnf ++ (o.traces.map fun (_, _, learnt) => learnt)
  o.traces.all fun (c, steps, learnt) => Cdcl.checkTrace db c steps learnt

#eval (List.range 60).foldl (fun n s => if checkTracesBig s then n else n + 1) 0
-- expect 0
