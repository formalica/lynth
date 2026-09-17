-- Star Battle scale pilot: 9x9 board, 1 star per row/column/3x3-region,
-- no touching (incl. diagonal). Same constraint shapes as the 4x4 pilot
-- (Bool cells, Fintype.card row/col counts, exact-one regions, adjacency
-- mutexes) at 81 cells. Regular 3x3 regions, one star (not two).
-- End-to-end measured at 5.1–5.3s; all solving remains inside `lynth`.
import Lynth
import Mathlib.Data.Fintype.Card

open Lynth.FinSearch

-- One star in row `r`.
def sbRow (s : Fin 9 → Fin 9 → Bool) (r : Fin 9) : Prop :=
  Fintype.card { c : Fin 9 // s r c = true } = 1

-- One star in column `c`.
def sbCol (s : Fin 9 → Fin 9 → Bool) (c : Fin 9) : Prop :=
  Fintype.card { r : Fin 9 // s r c = true } = 1

/-- Exactly one of nine cells holds (region/row/col rule). -/
def oneOf9 (a1 : Bool) (a2 : Bool) (a3 : Bool) (a4 : Bool) (a5 : Bool) (a6 : Bool) (a7 : Bool) (a8 : Bool) (a9 : Bool) : Prop :=
  (a1 = true ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = true ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = true ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = true ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = true ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = true ∧ a7 = false ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = true ∧ a8 = false ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = true ∧ a9 = false) ∨
  (a1 = false ∧ a2 = false ∧ a3 = false ∧ a4 = false ∧ a5 = false ∧ a6 = false ∧ a7 = false ∧ a8 = false ∧ a9 = true)

/-- Region 0: 3x3 block, one star. -/
def sbBox0 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 0 0) (s 0 1) (s 0 2) (s 1 0) (s 1 1) (s 1 2) (s 2 0) (s 2 1) (s 2 2)
/-- Region 1: 3x3 block, one star. -/
def sbBox1 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 0 3) (s 0 4) (s 0 5) (s 1 3) (s 1 4) (s 1 5) (s 2 3) (s 2 4) (s 2 5)
/-- Region 2: 3x3 block, one star. -/
def sbBox2 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 0 6) (s 0 7) (s 0 8) (s 1 6) (s 1 7) (s 1 8) (s 2 6) (s 2 7) (s 2 8)
/-- Region 3: 3x3 block, one star. -/
def sbBox3 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 3 0) (s 3 1) (s 3 2) (s 4 0) (s 4 1) (s 4 2) (s 5 0) (s 5 1) (s 5 2)
/-- Region 4: 3x3 block, one star. -/
def sbBox4 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 3 3) (s 3 4) (s 3 5) (s 4 3) (s 4 4) (s 4 5) (s 5 3) (s 5 4) (s 5 5)
/-- Region 5: 3x3 block, one star. -/
def sbBox5 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 3 6) (s 3 7) (s 3 8) (s 4 6) (s 4 7) (s 4 8) (s 5 6) (s 5 7) (s 5 8)
/-- Region 6: 3x3 block, one star. -/
def sbBox6 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 6 0) (s 6 1) (s 6 2) (s 7 0) (s 7 1) (s 7 2) (s 8 0) (s 8 1) (s 8 2)
/-- Region 7: 3x3 block, one star. -/
def sbBox7 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 6 3) (s 6 4) (s 6 5) (s 7 3) (s 7 4) (s 7 5) (s 8 3) (s 8 4) (s 8 5)
/-- Region 8: 3x3 block, one star. -/
def sbBox8 (s : Fin 9 → Fin 9 → Bool) : Prop :=
  oneOf9 (s 6 6) (s 6 7) (s 6 8) (s 7 6) (s 7 7) (s 7 8) (s 8 6) (s 8 7) (s 8 8)

-- Balanced conjunctions keep recognition and Decidable synthesis shallow.
set_option synthInstance.maxSize 4096 in
set_option maxHeartbeats 2000000 in
def starBattle : { s : Fin 9 → Fin 9 → Bool //
    (((((((sbRow s 0 ∧
    (sbRow s 1 ∧
    sbRow s 2)) ∧
    ((sbRow s 3 ∧
    sbRow s 4) ∧
    (sbRow s 5 ∧
    sbRow s 6))) ∧
    ((sbRow s 7 ∧
    (sbRow s 8 ∧
    sbCol s 0)) ∧
    ((sbCol s 1 ∧
    sbCol s 2) ∧
    (sbCol s 3 ∧
    sbCol s 4)))) ∧
    (((sbCol s 5 ∧
    (sbCol s 6 ∧
    sbCol s 7)) ∧
    ((sbCol s 8 ∧
    sbBox0 s) ∧
    (sbBox1 s ∧
    sbBox2 s))) ∧
    ((sbBox3 s ∧
    (sbBox4 s ∧
    sbBox5 s)) ∧
    ((sbBox6 s ∧
    sbBox7 s) ∧
    (sbBox8 s ∧
    ((s 0 0 && s 1 0) = false)))))) ∧
    ((((((s 0 0 && s 1 1) = false) ∧
    (((s 0 1 && s 1 0) = false) ∧
    ((s 0 1 && s 1 1) = false))) ∧
    ((((s 0 1 && s 1 2) = false) ∧
    ((s 0 2 && s 1 1) = false)) ∧
    (((s 0 2 && s 1 2) = false) ∧
    ((s 0 2 && s 1 3) = false)))) ∧
    ((((s 0 3 && s 1 2) = false) ∧
    (((s 0 3 && s 1 3) = false) ∧
    ((s 0 3 && s 1 4) = false))) ∧
    ((((s 0 4 && s 1 3) = false) ∧
    ((s 0 4 && s 1 4) = false)) ∧
    (((s 0 4 && s 1 5) = false) ∧
    ((s 0 5 && s 1 4) = false))))) ∧
    (((((s 0 5 && s 1 5) = false) ∧
    (((s 0 5 && s 1 6) = false) ∧
    ((s 0 6 && s 1 5) = false))) ∧
    ((((s 0 6 && s 1 6) = false) ∧
    ((s 0 6 && s 1 7) = false)) ∧
    (((s 0 7 && s 1 6) = false) ∧
    ((s 0 7 && s 1 7) = false)))) ∧
    ((((s 0 7 && s 1 8) = false) ∧
    (((s 0 8 && s 1 7) = false) ∧
    ((s 0 8 && s 1 8) = false))) ∧
    ((((s 1 0 && s 2 0) = false) ∧
    ((s 1 0 && s 2 1) = false)) ∧
    (((s 1 1 && s 2 0) = false) ∧
    ((s 1 1 && s 2 1) = false))))))) ∧
    (((((((s 1 1 && s 2 2) = false) ∧
    (((s 1 2 && s 2 1) = false) ∧
    ((s 1 2 && s 2 2) = false))) ∧
    ((((s 1 2 && s 2 3) = false) ∧
    ((s 1 3 && s 2 2) = false)) ∧
    (((s 1 3 && s 2 3) = false) ∧
    ((s 1 3 && s 2 4) = false)))) ∧
    ((((s 1 4 && s 2 3) = false) ∧
    (((s 1 4 && s 2 4) = false) ∧
    ((s 1 4 && s 2 5) = false))) ∧
    ((((s 1 5 && s 2 4) = false) ∧
    ((s 1 5 && s 2 5) = false)) ∧
    (((s 1 5 && s 2 6) = false) ∧
    ((s 1 6 && s 2 5) = false))))) ∧
    (((((s 1 6 && s 2 6) = false) ∧
    (((s 1 6 && s 2 7) = false) ∧
    ((s 1 7 && s 2 6) = false))) ∧
    ((((s 1 7 && s 2 7) = false) ∧
    ((s 1 7 && s 2 8) = false)) ∧
    (((s 1 8 && s 2 7) = false) ∧
    ((s 1 8 && s 2 8) = false)))) ∧
    ((((s 2 0 && s 3 0) = false) ∧
    (((s 2 0 && s 3 1) = false) ∧
    ((s 2 1 && s 3 0) = false))) ∧
    ((((s 2 1 && s 3 1) = false) ∧
    ((s 2 1 && s 3 2) = false)) ∧
    (((s 2 2 && s 3 1) = false) ∧
    ((s 2 2 && s 3 2) = false)))))) ∧
    ((((((s 2 2 && s 3 3) = false) ∧
    (((s 2 3 && s 3 2) = false) ∧
    ((s 2 3 && s 3 3) = false))) ∧
    ((((s 2 3 && s 3 4) = false) ∧
    ((s 2 4 && s 3 3) = false)) ∧
    (((s 2 4 && s 3 4) = false) ∧
    ((s 2 4 && s 3 5) = false)))) ∧
    ((((s 2 5 && s 3 4) = false) ∧
    (((s 2 5 && s 3 5) = false) ∧
    ((s 2 5 && s 3 6) = false))) ∧
    ((((s 2 6 && s 3 5) = false) ∧
    ((s 2 6 && s 3 6) = false)) ∧
    (((s 2 6 && s 3 7) = false) ∧
    ((s 2 7 && s 3 6) = false))))) ∧
    (((((s 2 7 && s 3 7) = false) ∧
    (((s 2 7 && s 3 8) = false) ∧
    ((s 2 8 && s 3 7) = false))) ∧
    ((((s 2 8 && s 3 8) = false) ∧
    ((s 3 0 && s 4 0) = false)) ∧
    (((s 3 0 && s 4 1) = false) ∧
    ((s 3 1 && s 4 0) = false)))) ∧
    (((((s 3 1 && s 4 1) = false) ∧
    ((s 3 1 && s 4 2) = false)) ∧
    (((s 3 2 && s 4 1) = false) ∧
    ((s 3 2 && s 4 2) = false))) ∧
    ((((s 3 2 && s 4 3) = false) ∧
    ((s 3 3 && s 4 2) = false)) ∧
    (((s 3 3 && s 4 3) = false) ∧
    ((s 3 3 && s 4 4) = false)))))))) ∧
    ((((((((s 3 4 && s 4 3) = false) ∧
    (((s 3 4 && s 4 4) = false) ∧
    ((s 3 4 && s 4 5) = false))) ∧
    ((((s 3 5 && s 4 4) = false) ∧
    ((s 3 5 && s 4 5) = false)) ∧
    (((s 3 5 && s 4 6) = false) ∧
    ((s 3 6 && s 4 5) = false)))) ∧
    ((((s 3 6 && s 4 6) = false) ∧
    (((s 3 6 && s 4 7) = false) ∧
    ((s 3 7 && s 4 6) = false))) ∧
    ((((s 3 7 && s 4 7) = false) ∧
    ((s 3 7 && s 4 8) = false)) ∧
    (((s 3 8 && s 4 7) = false) ∧
    ((s 3 8 && s 4 8) = false))))) ∧
    (((((s 4 0 && s 5 0) = false) ∧
    (((s 4 0 && s 5 1) = false) ∧
    ((s 4 1 && s 5 0) = false))) ∧
    ((((s 4 1 && s 5 1) = false) ∧
    ((s 4 1 && s 5 2) = false)) ∧
    (((s 4 2 && s 5 1) = false) ∧
    ((s 4 2 && s 5 2) = false)))) ∧
    ((((s 4 2 && s 5 3) = false) ∧
    (((s 4 3 && s 5 2) = false) ∧
    ((s 4 3 && s 5 3) = false))) ∧
    ((((s 4 3 && s 5 4) = false) ∧
    ((s 4 4 && s 5 3) = false)) ∧
    (((s 4 4 && s 5 4) = false) ∧
    ((s 4 4 && s 5 5) = false)))))) ∧
    ((((((s 4 5 && s 5 4) = false) ∧
    (((s 4 5 && s 5 5) = false) ∧
    ((s 4 5 && s 5 6) = false))) ∧
    ((((s 4 6 && s 5 5) = false) ∧
    ((s 4 6 && s 5 6) = false)) ∧
    (((s 4 6 && s 5 7) = false) ∧
    ((s 4 7 && s 5 6) = false)))) ∧
    ((((s 4 7 && s 5 7) = false) ∧
    (((s 4 7 && s 5 8) = false) ∧
    ((s 4 8 && s 5 7) = false))) ∧
    ((((s 4 8 && s 5 8) = false) ∧
    ((s 5 0 && s 6 0) = false)) ∧
    (((s 5 0 && s 6 1) = false) ∧
    ((s 5 1 && s 6 0) = false))))) ∧
    (((((s 5 1 && s 6 1) = false) ∧
    (((s 5 1 && s 6 2) = false) ∧
    ((s 5 2 && s 6 1) = false))) ∧
    ((((s 5 2 && s 6 2) = false) ∧
    ((s 5 2 && s 6 3) = false)) ∧
    (((s 5 3 && s 6 2) = false) ∧
    ((s 5 3 && s 6 3) = false)))) ∧
    (((((s 5 3 && s 6 4) = false) ∧
    ((s 5 4 && s 6 3) = false)) ∧
    (((s 5 4 && s 6 4) = false) ∧
    ((s 5 4 && s 6 5) = false))) ∧
    ((((s 5 5 && s 6 4) = false) ∧
    ((s 5 5 && s 6 5) = false)) ∧
    (((s 5 5 && s 6 6) = false) ∧
    ((s 5 6 && s 6 5) = false))))))) ∧
    (((((((s 5 6 && s 6 6) = false) ∧
    (((s 5 6 && s 6 7) = false) ∧
    ((s 5 7 && s 6 6) = false))) ∧
    ((((s 5 7 && s 6 7) = false) ∧
    ((s 5 7 && s 6 8) = false)) ∧
    (((s 5 8 && s 6 7) = false) ∧
    ((s 5 8 && s 6 8) = false)))) ∧
    ((((s 6 0 && s 7 0) = false) ∧
    (((s 6 0 && s 7 1) = false) ∧
    ((s 6 1 && s 7 0) = false))) ∧
    ((((s 6 1 && s 7 1) = false) ∧
    ((s 6 1 && s 7 2) = false)) ∧
    (((s 6 2 && s 7 1) = false) ∧
    ((s 6 2 && s 7 2) = false))))) ∧
    (((((s 6 2 && s 7 3) = false) ∧
    (((s 6 3 && s 7 2) = false) ∧
    ((s 6 3 && s 7 3) = false))) ∧
    ((((s 6 3 && s 7 4) = false) ∧
    ((s 6 4 && s 7 3) = false)) ∧
    (((s 6 4 && s 7 4) = false) ∧
    ((s 6 4 && s 7 5) = false)))) ∧
    ((((s 6 5 && s 7 4) = false) ∧
    (((s 6 5 && s 7 5) = false) ∧
    ((s 6 5 && s 7 6) = false))) ∧
    ((((s 6 6 && s 7 5) = false) ∧
    ((s 6 6 && s 7 6) = false)) ∧
    (((s 6 6 && s 7 7) = false) ∧
    ((s 6 7 && s 7 6) = false)))))) ∧
    ((((((s 6 7 && s 7 7) = false) ∧
    (((s 6 7 && s 7 8) = false) ∧
    ((s 6 8 && s 7 7) = false))) ∧
    ((((s 6 8 && s 7 8) = false) ∧
    ((s 7 0 && s 8 0) = false)) ∧
    (((s 7 0 && s 8 1) = false) ∧
    ((s 7 1 && s 8 0) = false)))) ∧
    ((((s 7 1 && s 8 1) = false) ∧
    (((s 7 1 && s 8 2) = false) ∧
    ((s 7 2 && s 8 1) = false))) ∧
    ((((s 7 2 && s 8 2) = false) ∧
    ((s 7 2 && s 8 3) = false)) ∧
    (((s 7 3 && s 8 2) = false) ∧
    ((s 7 3 && s 8 3) = false))))) ∧
    (((((s 7 3 && s 8 4) = false) ∧
    (((s 7 4 && s 8 3) = false) ∧
    ((s 7 4 && s 8 4) = false))) ∧
    ((((s 7 4 && s 8 5) = false) ∧
    ((s 7 5 && s 8 4) = false)) ∧
    (((s 7 5 && s 8 5) = false) ∧
    ((s 7 5 && s 8 6) = false)))) ∧
    (((((s 7 6 && s 8 5) = false) ∧
    ((s 7 6 && s 8 6) = false)) ∧
    (((s 7 6 && s 8 7) = false) ∧
    ((s 7 7 && s 8 6) = false))) ∧
    ((((s 7 7 && s 8 7) = false) ∧
    ((s 7 7 && s 8 8) = false)) ∧
    (((s 7 8 && s 8 7) = false) ∧
    ((s 7 8 && s 8 8) = false))))))))) } := by
  lynth

#print axioms starBattle
