import Lynth.Grind.Tactic
import Lean

example (m : Nat) (a b : Nat → Nat) (h : b = a) :
    b m = a m := by
  lynth_grind

example (m n : Nat) (a b : Nat → Nat → Nat) : b = a → m = n → i = j → b m i = a n j := by
  lynth_grind

example (m : Nat) (a : Nat → Nat) (f : (Nat → Nat) → (Nat → Nat)) (h : f a = a) :
    f a m = a m := by
  lynth_grind

example (m : Nat) (a : Nat → Nat) (f : (Nat → Nat) → (Nat → Nat)) (h : f a = a) :
    f a m = a m := by
  fail_if_success lynth_grind -funCC
  lynth_grind

example (a b : Nat) (g : Nat → Nat) (f : Nat → Nat → Nat) (h : f a = g) :
    f a b = g b := by
  lynth_grind

example (a b : Nat) (g : Nat → Nat) (f : Nat → Nat → Nat) (h : f a = g) :
    f a b = g b := by
  fail_if_success lynth_grind -funCC
  lynth_grind

namespace WithStructure

structure Test where
  apply: Unit → Prop

def test : Test := {
  apply := fun () => True
}

example : test.apply () := by
  lynth_grind [test]

end WithStructure

-- grind succeeds without the thunk
namespace WithoutThunk

structure Test where
  apply: Prop

def test : Test := {
  apply := True
}

example : test.apply := by
  lynth_grind [test]

end WithoutThunk

-- grind succeeds without structure
namespace WithoutStructure

def Test := Unit → Prop

def test : Test := fun () => True

example : test () := by
  lynth_grind [test]

end WithoutStructure

namespace Ex

opaque f : Nat → Nat → Nat
opaque g : Nat → Nat

example (a b c : Nat) : f a = g → b = c → f a b = g c := by
  fail_if_success lynth_grind
  simp_all

example (a b c : Nat) : f a = g → b = c → f a b = g c := by
  lynth_grind [funCC f, funCC g]

example (a b c : Nat) : f a = g → b = c → f a b = g c := by
  fail_if_success lynth_grind
  simp_all

attribute [grind funCC] f g

example (a b c : Nat) : f a = g → b = c → f a b = g c := by
  lynth_grind

example (a b c : Nat) : f a = g → b = c → f a b = g c := by
  fail_if_success lynth_grind -funCC
  lynth_grind

end Ex
