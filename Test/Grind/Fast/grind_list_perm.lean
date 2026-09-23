import Lynth.Grind.Tactic
open List

example : [3,1,4,2] ~ [2,4,1,3] := by lynth_grind

example (xs ys zs : List Nat) (h₁ : xs ⊆ ys) (h₂ : ys ~ zs) : xs ⊆ zs := by lynth_grind
example (xs ys zs : List Nat) (h₁ : xs <+ ys) (h₂ : ys ~ zs) : xs ⊆ zs := by lynth_grind
example (xs ys zs : List Nat) (h₁ : xs ~ ys) (h₂ : ys ~ zs) : xs ~ zs := by lynth_grind

example : List.range 10 ~ (List.range 5 ++ List.range' 5 5).reverse := by lynth_grind

variable [BEq α] [LawfulBEq α]

example (xs ys : List (List α)) (h : xs ~ ys) : xs.flatten ~ ys.flatten := by lynth_grind

example {l l' : List α} (hl : l ~ l') (_ : l'.Nodup) : l.Nodup := by lynth_grind

example {a b : α} {as bs : List α} :
    a :: as ++ b :: bs ~ b :: as ++ a :: bs := by lynth_grind

example (x y : α) (l : List α) :
    List.insert x (List.insert y l) ~ List.insert y (List.insert x l) := by lynth_grind
