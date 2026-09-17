-- Star Battle pilot: 1 star per row/col/2x2-region, no touching (incl. diagonal).
-- Exercises `Bool` grids, `Fintype.card` row/col counts, region
-- exact-one boolean structure, and adjacency mutexes end to end.
import Lynth
import Mathlib.Data.Fintype.Card

open Lynth.FinSearch

/-- One star in row `r`. -/
def sbRow (s : Fin 4 → Fin 4 → Bool) (r : Fin 4) : Prop :=
  Fintype.card { c : Fin 4 // s r c = true } = 1

/-- One star in column `c`. -/
def sbCol (s : Fin 4 → Fin 4 → Bool) (c : Fin 4) : Prop :=
  Fintype.card { r : Fin 4 // s r c = true } = 1

/-- Exactly one of four explicit cells holds (2x2 region rule). -/
def oneOf4 (a b c d : Bool) : Prop :=
  ((a && (b = false) && (c = false) && (d = false)) = true) ∨
  (((a = false) && b && (c = false) && (d = false)) = true) ∨
  (((a = false) && (b = false) && c && (d = false)) = true) ∨
  (((a = false) && (b = false) && (c = false) && d) = true)

def sbRegions (s : Fin 4 → Fin 4 → Bool) : Prop :=
  oneOf4 (s 0 0) (s 0 1) (s 1 0) (s 1 1) ∧
  oneOf4 (s 0 2) (s 0 3) (s 1 2) (s 1 3) ∧
  oneOf4 (s 2 0) (s 2 1) (s 3 0) (s 3 1) ∧
  oneOf4 (s 2 2) (s 2 3) (s 3 2) (s 3 3)

/-- Adjacent-row stars must be ≥ 2 columns apart (covers side + diagonal
touching; same-row pairs are excluded by the row counts). -/
def sbNoTouch (s : Fin 4 → Fin 4 → Bool) : Prop :=
  ((s 0 0 && s 1 0) = false) ∧ ((s 0 0 && s 1 1) = false) ∧
  ((s 0 1 && s 1 0) = false) ∧ ((s 0 1 && s 1 1) = false) ∧
  ((s 0 1 && s 1 2) = false) ∧ ((s 0 2 && s 1 1) = false) ∧
  ((s 0 2 && s 1 2) = false) ∧ ((s 0 2 && s 1 3) = false) ∧
  ((s 0 3 && s 1 2) = false) ∧ ((s 0 3 && s 1 3) = false) ∧
  ((s 1 0 && s 2 0) = false) ∧ ((s 1 0 && s 2 1) = false) ∧
  ((s 1 1 && s 2 0) = false) ∧ ((s 1 1 && s 2 1) = false) ∧
  ((s 1 1 && s 2 2) = false) ∧ ((s 1 2 && s 2 1) = false) ∧
  ((s 1 2 && s 2 2) = false) ∧ ((s 1 2 && s 2 3) = false) ∧
  ((s 1 3 && s 2 2) = false) ∧ ((s 1 3 && s 2 3) = false) ∧
  ((s 2 0 && s 3 0) = false) ∧ ((s 2 0 && s 3 1) = false) ∧
  ((s 2 1 && s 3 0) = false) ∧ ((s 2 1 && s 3 1) = false) ∧
  ((s 2 1 && s 3 2) = false) ∧ ((s 2 2 && s 3 1) = false) ∧
  ((s 2 2 && s 3 2) = false) ∧ ((s 2 2 && s 3 3) = false) ∧
  ((s 2 3 && s 3 2) = false) ∧ ((s 2 3 && s 3 3) = false)

/-- Witnessed by stars at (0,1),(1,3),(2,0),(3,2). -/
def starBattle : { s : Fin 4 → Fin 4 → Bool //
    sbRow s 0 ∧ sbRow s 1 ∧ sbRow s 2 ∧ sbRow s 3 ∧
    sbCol s 0 ∧ sbCol s 1 ∧ sbCol s 2 ∧ sbCol s 3 ∧
    sbRegions s ∧ sbNoTouch s } := by
  lynth

#print axioms starBattle
