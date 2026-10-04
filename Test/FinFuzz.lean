-- FinSearch differential: encoder verdicts vs brute force, both directions.
import Lynth.FinSearch.Syntax
import Lynth.FinSearch.Encode
import Lynth.Sat.Solver

open Lynth.FinSearch
open Lynth.FinSearch.Encode
open Lynth.Sat

set_option maxHeartbeats 57 in
def finFuzz_lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

set_option maxHeartbeats 99 in
/-- Random term over `na` atoms of cardinality `c` (leaves only). -/
def finFuzz_genTerm (s c na : Nat) : FTerm × Nat :=
  let s1 := finFuzz_lcg s
  if s1 % 2 == 0 then ((.lit c (s1 % c)), s1)
  else ((.var c (s1 % na)), s1)

set_option maxHeartbeats 681 in
/-- Random proposition (depth-bounded). -/
def genProp : Nat → Nat → Nat → Nat → FProp × Nat
  | s, 0, c, na =>
    let s1 := finFuzz_lcg s
    let (a, s2) := finFuzz_genTerm s1 c na
    let (b, s3) := finFuzz_genTerm s2 c na
    match s1 % 4 with
    | 0 => (.eq a b, s3)
    | 1 => (.ne a b, s3)
    | 2 => (.lt a b, s3)
    | _ => (.le a b, s3)
  | s, d + 1, c, na =>
    let s1 := finFuzz_lcg s
    match s1 % 5 with
    | 0 =>
      let (a, s2) := genProp s1 d c na
      let (b, s3) := genProp s2 d c na
      (.and [a, b], s3)
    | 1 =>
      let (a, s2) := genProp s1 d c na
      let (b, s3) := genProp s2 d c na
      (.or [a, b], s3)
    | 2 =>
      let (a, s2) := genProp s1 d c na
      (.not a, s2)
    | 3 =>
      let (a, s2) := finFuzz_genTerm s1 c na
      let (b, s3) := finFuzz_genTerm s2 c na
      let (d, s4) := finFuzz_genTerm s3 c na
      (.distinct [a, b, d], s4)
    | _ =>
      let (a, s2) := genProp s1 d c na
      let (b, s3) := genProp s2 d c na
      -- varied counts incl. 0 and over-count (k > n must be false)
      (.exactK [a, b] (s3 % 4), s3)

set_option maxHeartbeats 118 in
/-- All assignments: each of `na` atoms ranges over `c` values. -/
def finFuzz_allAssigns : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | na + 1, c =>
    (finFuzz_allAssigns na c).flatMap fun rest =>
      (List.range c).map fun v => v :: rest

set_option maxHeartbeats 47 in
/-- Brute-force validity. -/
def finFuzz_bruteValid (p : FProp) (na c : Nat) : Bool :=
  (finFuzz_allAssigns na c).all fun vals =>
    evalProp p (fun a => vals.getD a 0) (fun _ => false)

set_option maxHeartbeats 56 in
/-- SAT-model bit lookup. -/
def finFuzz_lookupAssign (m : Assignment) (v : Nat) : Bool :=
  match m.getD (v - 1) none with
  | some b => b
  | none => false

set_option maxHeartbeats 202 in
/-- Decode a model to atom values. -/
def finFuzz_decode (vmap : List ((Nat × Nat) × Nat)) (m : Assignment) :
    Nat → Nat :=
  fun a =>
    let bits := vmap.filterMap fun ((x, y), v) =>
      if x == a then some (y, v) else none
    match bits.find? fun (_, v) => finFuzz_lookupAssign m v with
    | some (w, _) => w
    | none => 0

set_option maxHeartbeats 217 in
/-- Agreement on one proposition: oracle vs brute force, with
counterexample validation on the SAT side (a model of `¬p` must
falsify `p` when decoded). -/
def checkProp (p : FProp) (na c : Nat) : Bool :=
  let brute := finFuzz_bruteValid p na c
  match runEncode (.not p) with
  | none => false
  | some (cnf, vmap, _) =>
    match Cdcl.cdclSolve cnf 10000 with
    | { result := some .unsat, .. } => brute
    | { result := some (.sat m), .. } =>
      (!brute) && decide (evalProp p (finFuzz_decode vmap m) (fun _ => false) == false)
    | { result := none, .. } => false

-- mismatch count over 60 random props (2 atoms, card 3); expect 0
#eval
  let seeds := List.range 60
  seeds.foldl (fun n s =>
    let (p, _) := genProp (s + 1) 3 3 2
    if checkProp p 2 3 then n else n + 1) 0
