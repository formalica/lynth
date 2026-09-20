-- Finite-domain pilot: cryptarithmetic (SEND + MORE = MONEY).
-- Witness is an INJECTIVE letter→digit map; spec evaluates the DECODED
-- arithmetic equation — combines all-diff with equation checking, not
-- just sum/length like SubsetSum.
-- NOTE: 10 digits, injective map over 8 letters — finite; brute-force applies.
-- TODO: failing until injective-map-with-equation synthesis lands in the pipeline.
import Lynth

/-- Letters: 0=S,1=E,2=N,3=D,4=M,5=O,6=R,7=Y. -/
def decode (f : Fin 8 → Fin 10) (digits : List (Fin 8)) : Nat :=
  digits.foldl (fun acc l => acc * 10 + (f l).val) 0

/-- Valid map: leading letters nonzero, all digits distinct, equation holds. -/
def cryptValid (f : Fin 8 → Fin 10) : Prop :=
  f 0 ≠ 0 ∧ f 4 ≠ 0 ∧
  (∀ l1 l2 : Fin 8, l1 ≠ l2 → f l1 ≠ f l2) ∧
  decode f [0,1,2,3] + decode f [4,5,6,1] = decode f [4,5,2,1,7]

/-- All letters, for computable checks. -/
def letters : List (Fin 8) := [0, 1, 2, 3, 4, 5, 6, 7]

/-- Computable check (mirrors `cryptValid`). -/
def cryptCheck (f : Fin 8 → Fin 10) : Bool :=
  (f 0 != 0) && (f 4 != 0) &&
  (letters.all fun l1 => letters.all fun l2 =>
    (l1 == l2) || (f l1 != f l2)) &&
  (decide (decode f [0,1,2,3] + decode f [4,5,6,1] = decode f [4,5,2,1,7]))

/-- The goal `lynth` must fill: the letter→digit map. -/
def cryptSol : { f : Fin 8 → Fin 10 // cryptValid f } := by
  lynth

/-- Etalon: S=9,E=5,N=6,D=7,M=1,O=0,R=8,Y=2 (9567+1085=10652). -/
def etalon : Fin 8 → Fin 10 := fun l =>
  match l.val with
  | 0 => 9 | 1 => 5 | 2 => 6 | 3 => 7 | 4 => 1 | 5 => 0 | 6 => 8 | _ => 2

-- The value computed by `lynth`:
#eval (cryptSol : Fin 8 → Fin 10)

-- The etalon digits:
#eval letters.map fun l => (etalon l).val

-- Runtime check: witness decodes a true equation.
#guard cryptCheck (cryptSol : Fin 8 → Fin 10)

/-- info: 'cryptSol' depends on axioms: [propext] -/
#guard_msgs in
#print axioms cryptSol
