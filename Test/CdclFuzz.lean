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

/-- Random CNF. -/
def genCNF : Nat → Nat → Nat → Nat → CNF × Nat
  | s, 0, _, _ => ([], s)
  | s, k + 1, nv, len =>
    let (cl, s1) := genClause s nv len
    let (rest, s2) := genCNF s1 k nv len
    (cl :: rest, s2)

/-- Agreement + model check for one seed. -/
def checkSeed (s : Nat) : Bool :=
  let (cnf, _) := genCNF (s + 1) 12 4 3
  match Cdcl.cdclSolve cnf 10000, solve cnf 10000 with
  | (some (.sat a), _), (.sat _) => checkSat cnf a
  | (some .unsat, _), .unsat => true
  | _, _ => false

-- mismatch count over 80 seeds; expect 0
#eval (List.range 80).foldl (fun n s => if checkSeed s then n else n + 1) 0
