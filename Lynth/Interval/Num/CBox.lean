import Lynth.Interval.Num.Ival
import Mathlib.Analysis.Complex.Basic

/-!
# Complex rectangles

`CBox` encloses a complex number by intervals for its real and imaginary parts.
See `docs/interval/02-numerics.md §4` and `docs/interval/10-complex.md`.
-/

namespace Lynth.Interval

structure CBox where
  re : Ival
  im : Ival
deriving Repr, Inhabited

namespace CBox

def Mem (B : CBox) (z : ℂ) : Prop := z.re ∈ B.re ∧ z.im ∈ B.im

instance : Membership ℂ CBox := ⟨CBox.Mem⟩

theorem mem_def {z : ℂ} {B : CBox} : z ∈ B ↔ z.re ∈ B.re ∧ z.im ∈ B.im := Iff.rfl

def top : CBox := ⟨Ival.top, Ival.top⟩
theorem mem_top (z : ℂ) : z ∈ top := ⟨Ival.mem_top _, Ival.mem_top _⟩

def isFinite (B : CBox) : Bool := B.re.isFinite && B.im.isFinite

/-- embedding of a real interval -/
def ofReal (I : Ival) : CBox := ⟨I, Ival.zero⟩
theorem mem_ofReal {x : ℝ} {I : Ival} (hx : x ∈ I) : (x : ℂ) ∈ ofReal I := by
  refine ⟨by rw [Complex.ofReal_re]; exact hx, by rw [Complex.ofReal_im]; exact Ival.mem_zero⟩

/-- the imaginary unit -/
def iI : CBox := ⟨Ival.zero, Ival.one⟩
theorem mem_I : Complex.I ∈ iI :=
  ⟨by rw [Complex.I_re]; exact Ival.mem_zero, by rw [Complex.I_im]; exact Ival.mem_one⟩

def add (p : Nat) (A B : CBox) : CBox := ⟨Ival.add p A.re B.re, Ival.add p A.im B.im⟩
theorem mem_add {p : Nat} {z w : ℂ} {A B : CBox} (hz : z ∈ A) (hw : w ∈ B) : z + w ∈ add p A B :=
  ⟨by rw [Complex.add_re]; exact Ival.mem_add hz.1 hw.1,
   by rw [Complex.add_im]; exact Ival.mem_add hz.2 hw.2⟩

def neg (A : CBox) : CBox := ⟨A.re.neg, A.im.neg⟩
theorem mem_neg {z : ℂ} {A : CBox} (hz : z ∈ A) : -z ∈ neg A :=
  ⟨by rw [Complex.neg_re]; exact Ival.mem_neg hz.1, by rw [Complex.neg_im]; exact Ival.mem_neg hz.2⟩

def sub (p : Nat) (A B : CBox) : CBox := ⟨Ival.sub p A.re B.re, Ival.sub p A.im B.im⟩
theorem mem_sub {p : Nat} {z w : ℂ} {A B : CBox} (hz : z ∈ A) (hw : w ∈ B) : z - w ∈ sub p A B :=
  ⟨by rw [Complex.sub_re]; exact Ival.mem_sub hz.1 hw.1,
   by rw [Complex.sub_im]; exact Ival.mem_sub hz.2 hw.2⟩

def conj (A : CBox) : CBox := ⟨A.re, A.im.neg⟩
theorem mem_conj {z : ℂ} {A : CBox} (hz : z ∈ A) : (starRingEnd ℂ) z ∈ conj A :=
  ⟨by rw [Complex.conj_re]; exact hz.1, by rw [Complex.conj_im]; exact Ival.mem_neg hz.2⟩

def mul (p : Nat) (A B : CBox) : CBox :=
  ⟨Ival.sub p (Ival.mul p A.re B.re) (Ival.mul p A.im B.im),
   Ival.add p (Ival.mul p A.re B.im) (Ival.mul p A.im B.re)⟩
theorem mem_mul {p : Nat} {z w : ℂ} {A B : CBox} (hz : z ∈ A) (hw : w ∈ B) : z * w ∈ mul p A B :=
  ⟨by rw [Complex.mul_re]; exact Ival.mem_sub (Ival.mem_mul hz.1 hw.1) (Ival.mem_mul hz.2 hw.2),
   by rw [Complex.mul_im]; exact Ival.mem_add (Ival.mem_mul hz.1 hw.2) (Ival.mem_mul hz.2 hw.1)⟩

/-- `|z|² = re² + im²` (dependency-aware squares) -/
def normSq (p : Nat) (A : CBox) : Ival := Ival.add p (Ival.sq p A.re) (Ival.sq p A.im)
theorem mem_normSq {p : Nat} {z : ℂ} {A : CBox} (hz : z ∈ A) : Complex.normSq z ∈ normSq p A := by
  rw [Complex.normSq_apply, ← pow_two, ← pow_two]
  exact Ival.mem_add (Ival.mem_sq hz.1) (Ival.mem_sq hz.2)

/-- `‖z‖` -/
def norm (p : Nat) (A : CBox) : Ival := Ival.sqrt p (normSq p A)
theorem mem_norm {p : Nat} {z : ℂ} {A : CBox} (hz : z ∈ A) : ‖z‖ ∈ norm p A := by
  rw [Complex.norm_def]; exact Ival.mem_sqrt (mem_normSq hz)

/-- `z⁻¹ = conj z / |z|²` (Mathlib: `0⁻¹ = 0`) -/
def inv (p : Nat) (A : CBox) : CBox :=
  let n := normSq p A
  if n.pos then ⟨Ival.div p A.re n, Ival.div p A.im.neg n⟩ else top
theorem mem_inv {p : Nat} {z : ℂ} {A : CBox} (hz : z ∈ A) : z⁻¹ ∈ inv p A := by
  unfold inv
  simp only
  split
  · refine ⟨?_, ?_⟩
    · rw [Complex.inv_re]; exact Ival.mem_div hz.1 (mem_normSq hz)
    · rw [Complex.inv_im, neg_div]
      have := Ival.mem_div (p := p) (Ival.mem_neg hz.2) (mem_normSq (p := p) hz)
      rwa [neg_div] at this
  · exact mem_top _

def div (p : Nat) (A B : CBox) : CBox := mul p A (inv p B)
theorem mem_div {p : Nat} {z w : ℂ} {A B : CBox} (hz : z ∈ A) (hw : w ∈ B) : z / w ∈ div p A B := by
  rw [div_eq_mul_inv]; exact mem_mul hz (mem_inv hw)

/-- natural power by repeated multiplication (binary) -/
def npowAux (p : Nat) (A : CBox) : Nat → Nat → CBox
  | 0, _ => top
  | _ + 1, 0 => ⟨Ival.one, Ival.zero⟩
  | fuel + 1, n + 1 =>
    if (n + 1) % 2 = 0 then
      let B := npowAux p A fuel ((n + 1) / 2)
      mul p B B
    else mul p A (npowAux p A fuel n)

def npow (p : Nat) (A : CBox) (n : Nat) : CBox := npowAux p A (2 * Nat.log2 n + 4) n

theorem mem_npowAux {p : Nat} {z : ℂ} {A : CBox} (hz : z ∈ A) :
    ∀ fuel n, z ^ n ∈ npowAux p A fuel n
  | 0, _ => mem_top _
  | _ + 1, 0 => by
    simp only [npowAux, pow_zero]
    exact ⟨by rw [Complex.one_re]; exact Ival.mem_one, by rw [Complex.one_im]; exact Ival.mem_zero⟩
  | fuel + 1, n + 1 => by
    unfold npowAux
    split
    · rename_i h
      have hB := mem_npowAux (p := p) (A := A) hz fuel ((n + 1) / 2)
      have := mem_mul (p := p) hB hB
      rw [← pow_add] at this
      have hn : (n + 1) / 2 + (n + 1) / 2 = n + 1 := by omega
      rwa [hn] at this
    · have := mem_mul (p := p) hz (mem_npowAux (p := p) (A := A) hz fuel n)
      rwa [← pow_succ'] at this

theorem mem_npow {p : Nat} {z : ℂ} {A : CBox} (hz : z ∈ A) (n : Nat) : z ^ n ∈ npow p A n :=
  mem_npowAux hz _ n

end CBox

end Lynth.Interval
