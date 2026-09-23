import Lynth.Grind.Tactic
open Lean Grind Std

variable [Field α] [LT α] [LE α] [LawfulOrderLT α] [IsLinearOrder α] [OrderedRing α]

example (x : α) : x ≥ 1/3 → x ≥ 0 := by lynth_grind
example (x : α) : x ≥ 1/3 → x ≥ 1/4 := by lynth_grind
example : (1/3 : α) ≥ 0 := by lynth_grind
example : (2/3 : α) ≥ 1/3 := by lynth_grind
example (x : α) : x + 1/3 ≤ x + 1/2 := by lynth_grind
example (x : α) (h : x ≤ 7/5) : 5*x ≤ 7 := by lynth_grind
example (x : α) (h : 3*x ≤ 7) : x ≤ 7/3 := by lynth_grind
example (x y : α) (h : x ≤ y - 1/3) : x + 1/6 ≤ y - 1/6 := by lynth_grind
example (x y : α) (h : x < y) : x + 1/3 < y + 1/3 := by lynth_grind
example (x : α) : x ≤ x + 1/7 := by lynth_grind
example (x : α) (h : x ≤ 1/4) : x - 1/3 ≤ -1/12 := by lynth_grind
example (x : α) (h : x ≤ x - 1/3) : False := by lynth_grind
example : (1/3 : α) ≤ 2/3 := by lynth_grind
example : (1/3 : α) ≤ (2/5 : α) := by lynth_grind
example (x y : α) (h : x ≤ y - (1/3 : α)) : x + (1/6 : α) ≤ y - (1/6 : α) := by lynth_grind
example (x : α) (h : x ≤ (1/4 : α)) : x - (1/3 : α) ≤ (-1/12 : α) := by lynth_grind
example (x : α) (h : x ≤ x - (1/5 : α)) : False := by lynth_grind
