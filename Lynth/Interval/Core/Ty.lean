import Lynth.Interval.Num.CBox
import Lynth.Interval.Num.NIval

/-!
# Value types of the interval AST

`Ty` indexes the typed expression language: natural numbers, reals and complex
numbers, with their semantic carriers (`Ty.Val`) and enclosures (`Ty.Enc`).
See `docs/interval/03-expr-registry.md §1`.
-/

namespace Lynth.Interval

inductive Ty | nat | real | cplx
deriving Repr, DecidableEq, Inhabited

namespace Ty

/-- semantic carrier -/
@[reducible] def Val : Ty → Type
  | .nat => ℕ
  | .real => ℝ
  | .cplx => ℂ

/-- computational enclosure -/
@[reducible] def Enc : Ty → Type
  | .nat => NIval
  | .real => Ival
  | .cplx => CBox

/-- membership of a value in an enclosure -/
def Mem : (t : Ty) → t.Enc → t.Val → Prop
  | .nat, I, n => n ∈ I
  | .real, I, x => x ∈ I
  | .cplx, B, z => z ∈ B

/-- the trivial enclosure -/
def top : (t : Ty) → t.Enc
  | .nat => NIval.top
  | .real => Ival.top
  | .cplx => CBox.top

theorem mem_top : (t : Ty) → (v : t.Val) → t.Mem (t.top) v
  | .nat, n => NIval.mem_top n
  | .real, x => Ival.mem_top x
  | .cplx, z => CBox.mem_top z

instance instAddCommMonoid : (t : Ty) → AddCommMonoid t.Val
  | .nat => inferInstanceAs (AddCommMonoid ℕ)
  | .real => inferInstanceAs (AddCommMonoid ℝ)
  | .cplx => inferInstanceAs (AddCommMonoid ℂ)

/-- exact zero enclosure -/
def zeroE : (t : Ty) → t.Enc
  | .nat => NIval.pt 0
  | .real => Ival.zero
  | .cplx => ⟨Ival.zero, Ival.zero⟩

/-- sum of enclosures at precision `p` -/
def addE : (t : Ty) → Nat → t.Enc → t.Enc → t.Enc
  | .nat, _, I, J => NIval.add I J
  | .real, p, I, J => Ival.add p I J
  | .cplx, p, A, B => CBox.add p A B

theorem mem_zeroE : (t : Ty) → t.Mem t.zeroE 0
  | .nat => NIval.mem_pt 0
  | .real => Ival.mem_zero
  | .cplx => ⟨by rw [Complex.zero_re]; exact Ival.mem_zero, by rw [Complex.zero_im]; exact Ival.mem_zero⟩

theorem mem_addE : (t : Ty) → {p : Nat} → {A B : t.Enc} → {a b : t.Val} →
    t.Mem A a → t.Mem B b → t.Mem (t.addE p A B) (a + b)
  | .nat, _, _, _, _, _, ha, hb => NIval.mem_add ha hb
  | .real, _, _, _, _, _, ha, hb => Ival.mem_add ha hb
  | .cplx, _, _, _, _, _, ha, hb => CBox.mem_add ha hb

/-- is the enclosure bounded -/
def isFinite : (t : Ty) → t.Enc → Bool
  | .nat, I => I.hi.isSome
  | .real, I => I.isFinite
  | .cplx, B => B.isFinite

end Ty

end Lynth.Interval
