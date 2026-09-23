import Lynth.Grind.Tactic
/-
The `ite` and `dite` propagators in `grind` were not internalizing
their children using the correct parent information. Several examples
in this file were failing because of this bug.
-/

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.IntModule α] [DecidableLE α] [Lean.Grind.OrderedAdd α]
    (a b c d : α)
    (h : ¬(-(a - b)) ≤ ((-(a - c)) + -(c - d)) + -(b - d))
    (h_1 : b - d ≤ -(b - d)) : False := by
  lynth_grind

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.IntModule α] [DecidableLE α] [Lean.Grind.OrderedAdd α]
    (a b c d : α)
    (h : ¬(-(a - b)) ≤ ((-(a - c)) + -(c - d)) + if b - d ≤ -(b - d) then -(b - d) else b - d)
    (h_1 : b - d ≤ -(b - d)) : False := by
  lynth_grind

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α]
    (a b c : α)
    (h : a ≤ a + if b ≤ c then (-1 : α) else (-2))
    (h_1 : b ≤ c)
    : False := by
  lynth_grind

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α]
    (a b c : α)
    (h : a ≤ a + if b ≤ c then (-1 : α) else (-2))
    : False := by
  lynth_grind

example [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α] (a b c : α) :
  (if a - b ≤ -(a - b) then -(a - b) else a - b) ≤
  ((if a - c ≤ -(a - c) then -(a - c) else a - c) + if c - d ≤ -(c - d) then -(c - d) else c - d) +
    if b - d ≤ -(b - d) then -(b - d) else b - d := by
  lynth_grind

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.IntModule α] [DecidableLE α] [Lean.Grind.OrderedAdd α]
    (a b c d : α)
    (h : ¬(-(a - b)) ≤ ((-(a - c)) + -(c - d)) + -(b - d))
    (h_1 : b - d ≤ -(b - d)) : False := by
  lynth_grind -order

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.IntModule α] [DecidableLE α] [Lean.Grind.OrderedAdd α]
    (a b c d : α)
    (h : ¬(-(a - b)) ≤ ((-(a - c)) + -(c - d)) + if b - d ≤ -(b - d) then -(b - d) else b - d)
    (h_1 : b - d ≤ -(b - d)) : False := by
  lynth_grind -order

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α]
    (a b c : α)
    (h : a ≤ a + if b ≤ c then (-1 : α) else (-2))
    (h_1 : b ≤ c)
    : False := by
  lynth_grind -order

example {α : Type _} [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α]
    [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α]
    (a b c : α)
    (h : a ≤ a + if b ≤ c then (-1 : α) else (-2))
    : False := by
  lynth_grind -order

example [LE α] [LT α] [Std.IsLinearOrder α] [Std.LawfulOrderLT α] [Lean.Grind.CommRing α] [DecidableLE α] [Lean.Grind.OrderedRing α] (a b c : α) :
  (if a - b ≤ -(a - b) then -(a - b) else a - b) ≤
  ((if a - c ≤ -(a - c) then -(a - c) else a - c) + if c - d ≤ -(c - d) then -(c - d) else c - d) +
    if b - d ≤ -(b - d) then -(b - d) else b - d := by
  lynth_grind -order
