-- Farkas validation: every FM refutation certificate verifies.
import Lynth.Arith.Fourier

open Lynth.Arith.Fourier

-- hand certificates verify
#eval checkCert [mkLe [1] (-1) 2 0, mkLe [-1] 2 2 1] [1, 1]
-- expect true

-- wrong weights do not verify (negative weight)
#eval !(checkCert [mkLe [1] (-1) 2 0, mkLe [-1] 2 2 1] [-1, 1])
-- expect true

-- wrong weights do not verify (LHS does not vanish)
#eval !(checkCert [mkLe [1] (-1) 2 0, mkLe [-1] 2 2 1] [1, 0])
-- expect true

-- wrong length does not verify
#eval !(checkCert [mkLe [1] (-1) 2 0] [1, 1])
-- expect true

/-- Fuzz: `solve`'s certificates always validate. Returns violations. -/
def lcg (s : Nat) : Nat := (1103515245 * s + 12345) % 2147483648

def genLeC : Nat → Nat → Nat → List LeC × Nat
  | s, 0, _ => ([], s)
  | s, k + 1, idx =>
    let c : List Rat :=
      (List.range 3).map fun j => ((lcg (s + j + k * 7) % 5 : Nat) : Rat) - 2
    let c0 : Rat := ((lcg (s + 99 + k) % 7 : Nat) : Rat) - 3
    let (rest, s') := genLeC (lcg (s + k)) k (idx + 1)
    ((mkLe c c0 5 idx) :: rest, s')

def checkSeed (i : Nat) : Bool :=
  let (sys, _) := genLeC (i + 1) 5 0
  match solve sys 128 with
  | some cert => checkCert sys cert
  | none => true

#eval (List.range 80).foldl (fun n i => if checkSeed i then n else n + 1) 0
-- expect 0
