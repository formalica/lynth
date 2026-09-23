import Lynth.Grind.Tactic
@[expose] public section -- TODO: remove after we fix congr_eq

def f (a : Option Nat) (h : a ≠ none) : Nat :=
 match a with
 | some a => a
 | none => by lynth_grind

def g (a : Option Nat) : Nat :=
  match h : a with
  | none => 1
  | some _ => f a (by lynth_grind) + 1

example : g a > 0 := by
  unfold g
  lynth_grind
