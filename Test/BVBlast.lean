-- Bit-blast differential: oracle verdicts vs brute force, both directions.
import Lynth.BV.Blast
import Lynth.Sat.Solver

open Lynth.BV
open Lynth.Sat

def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

set_option maxRecDepth 10000 in
/-- Random leaf: constant or variable. -/
def genBase (s w na : Nat) : BvTerm × Nat :=
  let s1 := lcg s
  if s1 % 2 == 0 then ((.const w (s1 % 2 ^ w)), s1)
  else ((.var w (s1 % na)), s1)

/-- Random term (width `w`, atoms below `na`), threaded seed. -/
def genTerm : Nat → Nat → Nat → Nat → BvTerm × Nat
  | s, 0, w, na => genBase s w na
  | s, d + 1, w, na =>
    let s1 := lcg s
    let k := s1 % 5
    if k == 0 then
      let (a, s2) := genTerm s1 d w na
      let (b, s3) := genTerm s2 d w na
      (.and a b, s3)
    else if k == 1 then
      let (a, s2) := genTerm s1 d w na
      let (b, s3) := genTerm s2 d w na
      (.or a b, s3)
    else if k == 2 then
      let (a, s2) := genTerm s1 d w na
      let (b, s3) := genTerm s2 d w na
      (.xor a b, s3)
    else if k == 3 then
      let (a, s2) := genTerm s1 d w na
      (.not a, s2)
    else
      let (a, s2) := genTerm s1 d w na
      let (b, s3) := genTerm s2 d w na
      (.add a b, s3)

/-- All assignments: each of `na` atoms ranges over `2^w` values. -/
def allAssigns : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | na + 1, w =>
    (allAssigns na w).flatMap fun rest =>
      (List.range (2 ^ w)).map fun v => v :: rest

/-- Assignment function from value list. -/
def assignOf (vals : List Nat) : Nat → Nat :=
  fun a => vals.getD a 0

/-- Brute-force validity of `t1 = t2`. -/
def bruteValid (t1 t2 : BvTerm) (na w : Nat) : Bool :=
  (allAssigns na w).all fun vals =>
    decide (eval t1 (assignOf vals) == eval t2 (assignOf vals))

/-- SAT-model lookup (default false; complete models never miss). -/
def lookupAssign (m : Assignment) (v : Nat) : Bool :=
  match m.getD (v - 1) none with
  | some b => b
  | none => false

/-- Decode a CDCL model to atom values via the var map. -/
def decode (vmap : List ((Nat × Nat) × Nat)) (m : Assignment)
    (w : Nat) : Nat → Nat :=
  fun a => (List.range w).foldl (fun acc i =>
    let v := match vmap.find? fun ((x, y), _) => x == a && y == i with
      | some (_, v) => v
      | none => 0
    if v == 0 then acc
    else if lookupAssign m v then acc + 2 ^ i else acc) 0

/-- Agreement on one equation pair: oracle vs brute force, with
counterexample validation on the SAT side. -/
def checkPair (t1 t2 : BvTerm) (na w : Nat) : Bool :=
  let brute := bruteValid t1 t2 na w
  match runBlast (blastNeq t1 t2) with
  | none => false
  | some (cnf, vmap) =>
    match Cdcl.cdclSolve cnf 10000 with
    | { result := some .unsat, .. } => brute
    | { result := some (.sat m), .. } =>
      (!brute) &&
        decide (eval t1 (decode vmap m w) != eval t2 (decode vmap m w))
    | { result := none, .. } => false

-- mismatch count over 60 random equations (width 3, 2 atoms); expect 0
#eval
  let seeds := List.range 60
  seeds.foldl (fun n s =>
    let (t1, s1) := genTerm (s + 1) 3 3 2
    let (t2, _) := genTerm s1 3 3 2
    if checkPair t1 t2 2 3 then n else n + 1) 0

-- regression: shared subterms (duplicate literals) decide correctly
#eval Lynth.BV.checkValidEq (.xor (.var 4 0) (.var 4 0)) (.const 4 0) 10000
-- expect true

#eval Lynth.BV.checkValidEq (.and (.var 4 0) (.var 4 0)) (.var 4 0) 10000
-- expect true

#eval !(Lynth.BV.checkValidEq (.var 4 0) (.const 4 1) 10000)
-- expect true (0 ≠ 1 is satisfiable, so the equation is not valid)
