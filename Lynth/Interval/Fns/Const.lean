import Lynth.Interval.Fns.Log
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Constants: Euler–Mascheroni `γ`

`harmonic N - log (N + 1) < γ < harmonic N - log N` (Mathlib's monotone
bracketing sequences), `N = 128`: width `≈ 1/N`.  Low accuracy; a sharper
Euler–Maclaurin enclosure is future work (`docs/interval/04 §13`).
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-- enclosure of `harmonic n` -/
def harmIval (w : Nat) : Nat → Ival
  | 0 => Ival.zero
  | n + 1 => Ival.add w (harmIval w n) (Ival.inv w (Ival.pt (Dy.ofNat (n + 1))))

theorem mem_harmIval (w : Nat) : ∀ n, ((harmonic n : ℚ) : ℝ) ∈ harmIval w n
  | 0 => by simpa [harmIval] using Ival.mem_zero
  | n + 1 => by
    rw [harmonic_succ]
    have h := Ival.mem_inv (p := w) (Ival.mem_pt (Dy.ofNat (n + 1)))
    simp only [toReal_def, toRat_ofNat] at h
    push_cast at h ⊢
    exact Ival.mem_add (mem_harmIval w n) h

def eulerIvalN (c : Ctx) (N : Nat) : Ival :=
  let w := c.prec + 8
  let H := harmIval w N
  let lo := Ival.sub w H (logIval c (Ival.pt (Dy.ofNat (N + 1))))
  let hi := Ival.sub w H (logIval c (Ival.pt (Dy.ofNat N)))
  ⟨lo.lo, hi.hi⟩

theorem mem_eulerIvalN {c : Ctx} (hc : c.Valid) {N : Nat} (hN : N ≠ 0) :
    Real.eulerMascheroniConstant ∈ eulerIvalN c N := by
  have hH := mem_harmIval (c.prec + 8) N
  have hl := Ival.mem_sub (p := c.prec + 8) hH (mem_logIval hc (Ival.mem_pt (Dy.ofNat (N + 1))))
  have hh := Ival.mem_sub (p := c.prec + 8) hH (mem_logIval hc (Ival.mem_pt (Dy.ofNat N)))
  have e1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant N
  have e2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' N
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq', if_neg hN] at e1 e2
  simp only [toReal_def, toRat_ofNat, Nat.cast_add, Nat.cast_one, Rat.cast_add, Rat.cast_natCast,
    Rat.cast_one] at hl hh
  refine ⟨fun l hlo => ?_, fun h hhi => ?_⟩
  · exact le_trans (hl.1 l hlo) e1.le
  · exact le_trans e2.le (hh.2 h hhi)

def eulerIval (c : Ctx) : Ival := eulerIvalN c 128

theorem mem_eulerIval {c : Ctx} (hc : c.Valid) : Real.eulerMascheroniConstant ∈ eulerIval c :=
  mem_eulerIvalN hc (by decide)

@[lynth_fn] def eulerR : Fn0 .real where
  name := "eulerMascheroni"
  graph y := y = Real.eulerMascheroniConstant
  exu := exu_eq₀ _
  ev := eulerIval
  sound := fun _ _ hc hy => by obtain rfl := hy; exact mem_eulerIval hc
  cost := 400

end Lynth.Interval.Fns
