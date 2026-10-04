-- Finite-domain pilot: bounded planning (action sequence).
-- Two toggle lights, start (off,off), goal (on,on); witness is a LIST
-- of actions checked by FOLDING the transition function — state-update
-- dynamics, unlike ShortestPath's static vertex adjacency.
-- NOTE: plans bounded by length ≤ 2 over 2 actions — finite
-- (bounded model checking); brute-force applies.
-- TODO: failing until plan-style fold synthesis lands in the pipeline.
import Lynth

set_option maxHeartbeats 82 in
/-- Toggle light 0 or light 1. -/
def apply (s : Bool × Bool) (a : Fin 2) : Bool × Bool :=
  if a.val == 0 then (!s.1, s.2) else (s.1, !s.2)

set_option maxHeartbeats 21 in
/-- Valid plan: at most 2 actions, folding from (off,off) reaches (on,on). -/
def planValid (acts : List (Fin 2)) : Prop :=
  acts.length ≤ 2 ∧ acts.foldl apply (false, false) = (true, true)

set_option maxHeartbeats 74 in
/-- Computable check (mirrors `planValid`). -/
def planCheck (acts : List (Fin 2)) : Bool :=
  decide (acts.length ≤ 2) && (acts.foldl apply (false, false) == (true, true))

set_option maxHeartbeats 128 in
/-- The goal `lynth` must fill: the action list. -/
def planSol : { acts : List (Fin 2) // planValid acts } := by
  lynth
/-- info: 'planSol' does not depend on any axioms -/
#guard_msgs in
#print axioms planSol

set_option maxHeartbeats 34 in
/-- Etalon: toggle 0, then toggle 1. -/
def togglePlan_etalon : List (Fin 2) := [0, 1]

-- The value computed by `lynth`:
#eval (planSol : List (Fin 2))

-- The togglePlan_etalon:
#eval togglePlan_etalon

-- Runtime checks: witness reaches the goal within the bound.
#guard planCheck (planSol : List (Fin 2))
#guard (planSol : List (Fin 2)).length ≤ 2

