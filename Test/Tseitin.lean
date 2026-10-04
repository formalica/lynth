-- Tseitin oracle validation: `isTautology` vs brute-force truth tables.
import Lynth.Sat.Encode

open Lynth.Sat.Encode

set_option maxHeartbeats 145 in
/-- Reference semantics of skeletons. -/
def evalForm : PropForm → (Nat → Bool) → Bool
  | .atom i, v => v i
  | .tru, _ => true
  | .fls, _ => false
  | .neg f, v => !(evalForm f v)
  | .conj a b, v => evalForm a v && evalForm b v
  | .disj a b, v => evalForm a v || evalForm b v
  | .imp a b, v => !(evalForm a v) || evalForm b v

set_option maxHeartbeats 119 in
/-- Brute-force validity over `n` atoms. -/
def tseitin_bruteValid (f : PropForm) (n : Nat) : Bool :=
  (List.range (2 ^ n)).all fun mask =>
    evalForm f fun i => decide ((mask / 2 ^ i) % 2 == 1)

set_option maxHeartbeats 54 in
def tseitin_lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

set_option maxHeartbeats 415 in
/-- Random skeleton, depth-bounded, atoms in `0..3`. -/
def genForm : Nat → Nat → PropForm × Nat
  | s, 0 =>
    let s1 := tseitin_lcg s
    ((.atom (s1 % 3)), s1)
  | s, d + 1 =>
    let s1 := tseitin_lcg s
    match s1 % 7 with
    | 0 => ((.atom (s1 % 3)), s1)
    | 1 => (.tru, s1)
    | 2 => (.fls, s1)
    | 3 =>
      let (f, s2) := genForm s1 d
      (.neg f, s2)
    | 4 =>
      let (a, s2) := genForm s1 d
      let (b, s3) := genForm s2 d
      (.conj a b, s3)
    | 5 =>
      let (a, s2) := genForm s1 d
      let (b, s3) := genForm s2 d
      (.disj a b, s3)
    | _ =>
      let (a, s2) := genForm s1 d
      let (b, s3) := genForm s2 d
      (.imp a b, s3)

set_option maxHeartbeats 68 in
/-- Agreement on one seed. -/
def tseitin_checkSeed (s : Nat) : Bool :=
  let (f, _) := genForm (s + 1) 4
  isTautology f 3 10000 == tseitin_bruteValid f 3

-- mismatches over 200 seeds; expect 0
#eval (List.range 200).foldl (fun n s => if tseitin_checkSeed s then n else n + 1) 0
