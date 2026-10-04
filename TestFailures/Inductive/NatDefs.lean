import Lynth

inductive AddInd : Nat → Nat → Nat → Prop where
  | zero : AddInd 0 0 0
  | incLeft : AddInd a b c → AddInd a.succ b c.succ
  | incRight : AddInd a b c → AddInd a b.succ c.succ

def add_func :
    { f : Nat → Nat → Nat //
      ∀ a b, AddInd a b (f a b) } := by
  lynth
#print axioms add_func
