import Lynth.Grind.Tactic
open Lean Grind

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    (a b c : α) : a ≤ b → b ≤ c → c < a → False := by
  lynth_grind

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α]
    (a b c d : α) : a ≤ b → b ≤ c → c < d → d ≤ a → False := by
  lynth_grind

example [LE α] [Std.IsPreorder α]
    (a b c : α) : a ≤ b → b ≤ c → a ≤ c := by
  lynth_grind

example [LE α] [Std.IsPreorder α]
    (a b c d : α) : a ≤ b → b ≤ c → c ≤ d → a ≤ d := by
  lynth_grind

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) : a ≤ b → b ≤ c → c < a → False := by
  lynth_grind -linarith

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b : α) : a ≤ 5 → b ≤ 8 → a > 6 ∨ b > 10 → False := by
  lynth_grind -linarith (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [CommRing α] [OrderedRing α]
    (a b c : α) : a + b*c + 2*c ≤ 5 → a + c > 5 - c - c*b → False := by
  lynth_grind -linarith (splits := 0)

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) : a - b ≤ 5 → -c + b ≤ -3 → c < a - 2 → False := by
  lynth_grind -linarith

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) : a - b ≤ 5 → -c + b < -3 → c < a - 2 → False := by
  lynth_grind -linarith

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) : a - b < 5 → -c + b < -3 → c < a - 2 → False := by
  lynth_grind -linarith

example [LE α] [LT α] [Std.LawfulOrderLT α] [Std.IsPreorder α] [Ring α] [OrderedRing α]
    (a b c : α) : a - b < 5 → -c + b ≤ -3 → c < a - 2 → False := by
  lynth_grind -linarith

example (a b c : Int) : a - b ≤ 5 → -c + b ≤ -3 → c < a - 2 → False := by
  lynth_grind -linarith -lia

example (a b : Int) (h : a + b > 5) : (if a + b ≤ 0 then b else a) = a := by
  lynth_grind -linarith -lia (splits := 0)
