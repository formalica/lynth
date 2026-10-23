module

public import Init.Data.Cast
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Option.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Fns.Special.Eta
public import Lynth.Interval.Integral.Eval
public import Lynth.Interval.Integral.Exp
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Integral.Eval
import all Lynth.Interval.Fns.Special.Bounds

/-! Analytic bounds for entire special functions. These bounds do not evaluate
an oscillatory real phase or cancel the pole of zeta numerically. -/

namespace Lynth.Interval.Integral

open Intgrl Fns SpecialFunctions

@[expose] public def etaGlobalMagnitude (c : Ctx) (Z : CBox) : Option Dy := do
  let lo ← Z.re.lo
  let m := etaShift lo.toRat
  if !(0 < lo.toRat + m) then none else
    let n := 4*m
    (Ival.add c.prec (Ival.ofRat c.prec ((n : ℚ)*(n+1 : ℚ)^m)) (etaCError c Z m n)).hi

theorem etaGlobalMagnitude_sound {c : Ctx} {z : ℂ} {Z : CBox} {M : Dy}
    (hz : z ∈ Z) (h : etaGlobalMagnitude c Z = some M) :
    ‖Complex.dirichletEta z‖ ≤ M.toReal := by
  unfold etaGlobalMagnitude at h
  cases hlo : Z.re.lo with
  | none => simp [hlo] at h
  | some lo =>
    simp only [hlo, bind, Option.bind] at h
    split at h
    · simp at h
    · rename_i hp
      have hp' : (0 : ℚ) < lo.toRat + etaShift lo.toRat := by simpa using hp
      have hpos : (0 : ℝ) < z.re + (etaShift lo.toRat : ℕ) := by
        have hb := hz.1.1 lo hlo
        have ht : (0 : ℝ) < lo.toReal + (etaShift lo.toRat : ℕ) := by
          rw [Dy.toReal_def]; exact_mod_cast hp'
        linarith
      apply (eta_growth z _ hpos).trans
      push_cast at h
      have hb := (Ival.mem_add (p := c.prec)
        (Ival.mem_ofRat c.prec ((4*etaShift lo.toRat : ℚ)*(4*etaShift lo.toRat+1 : ℚ)^(etaShift lo.toRat)))
        (mem_etaCError c hz (etaShift lo.toRat) (4*etaShift lo.toRat))).2 M h
      push_cast at hb
      exact hb

@[expose] public def specialMagnitude (c : Ctx) (op : Unary) (Z : CBox) : Option Dy :=
  match op with
  | .erf =>
    let y := Ival.abs Z.im
    (Ival.add c.prec Ival.one (Ival.mul c.prec (Ival.mul c.prec (Ival.ofRat c.prec 2) y)
      (fastExpIval c (Ival.sq c.prec y)))).hi
  | .si =>
    (Ival.mul c.prec (CBox.norm c.prec Z) (fastExpIval c (Ival.abs Z.im))).hi
  | .airyAi =>
    let x := Ival.abs Z.re
    let y := Ival.abs Z.im
    (Ival.mul c.prec (Ival.add c.prec (Ival.ofRat c.prec 2) x)
      (fastExpIval c (Ival.mul c.prec (Ival.add c.prec (Ival.add c.prec Ival.one x) y) y))).hi
  | .eta =>
    match (CBox.norm c.prec (CBox.sub c.prec Z (CBox.ofReal Ival.one))).hi with
    | some r =>
      if Dy.ltB r (Dy.ofNat 4) then
        (Ival.add c.prec c.ln2 (Ival.ofRat c.prec (r.toRat/(4-r.toRat)))).hi
      else etaGlobalMagnitude c Z
    | none => etaGlobalMagnitude c Z
  | _ => (CBox.norm c.prec (Unary.evalC c op Z)).hi

theorem specialMagnitude_sound {c : Ctx} (hc : c.Valid) (op : Unary)
    {z : ℂ} {Z : CBox} {M : Dy} (hz : z ∈ Z)
    (h : specialMagnitude c op Z = some M) : ‖op.complex z‖ ≤ M.toReal := by
  cases op with
  | erf =>
    apply (complex_bounds z).1.trans
    simpa only [sq_abs] using
      ((Ival.mem_add (p := c.prec) Ival.mem_one
        (Ival.mem_mul (Ival.mem_mul (by simpa using Ival.mem_ofRat c.prec 2) (Ival.mem_abs hz.2))
          (mem_fastExpIval c (Ival.mem_sq (Ival.mem_abs hz.2))))).2 M h)
  | si =>
    exact (complex_bounds z).2.1.trans
      ((Ival.mem_mul (p := c.prec) (CBox.mem_norm hz)
        (mem_fastExpIval c (Ival.mem_abs hz.2))).2 M h)
  | airyAi =>
    exact (airy_complex_vertical z).trans
      ((Ival.mem_mul (p := c.prec)
        (Ival.mem_add (Ival.mem_ofRat c.prec 2) (Ival.mem_abs hz.1))
        (mem_fastExpIval c (Ival.mem_mul
          (Ival.mem_add (Ival.mem_add Ival.mem_one (Ival.mem_abs hz.1)) (Ival.mem_abs hz.2))
          (Ival.mem_abs hz.2)))).2 M h)
  | eta =>
    simp only [specialMagnitude] at h
    split at h
    · rename_i r hr
      split at h
      · rename_i hlt
        have hz1 := CBox.mem_sub (p := c.prec) hz (CBox.mem_ofReal Ival.mem_one)
        have hb : ‖z-1‖ ≤ r.toReal := by
          simpa using (CBox.mem_norm (p := c.prec) hz1).2 r hr
        have hr4 : r.toReal < 4 := by simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB hlt
        have hcirc := eta_near_one z (hb.trans_lt hr4)
        have hn : ‖Complex.dirichletEta z‖ ≤ Real.log 2 + r.toReal/(4-r.toReal) := by
          have hd : (0 : ℝ) < 4-r.toReal := by linarith
          have hd' : (0 : ℝ) < 4-‖z-1‖ := by linarith
          have hb' : ‖z-1‖/(4-‖z-1‖) ≤ r.toReal/(4-r.toReal) := by
            apply (div_le_div_iff₀ hd' hd).2
            nlinarith
          have hh := norm_le_norm_sub_add (Complex.dirichletEta z) (Real.log 2 : ℂ)
          have hl : ‖(Real.log 2 : ℂ)‖ = Real.log 2 := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
          rw [hl] at hh
          linarith
        apply hn.trans
        simpa only [Dy.toReal_def, Rat.cast_div, Rat.cast_sub, Rat.cast_ofNat] using
          (Ival.mem_add (p := c.prec) hc.ln2_mem
            (Ival.mem_ofRat c.prec (r.toRat/(4-r.toRat)))).2 M h
      · exact etaGlobalMagnitude_sound hz h
    · exact etaGlobalMagnitude_sound hz h
  | _ => exact (CBox.mem_norm (p := c.prec) (unary_evalC_sound hc _ hz)).2 M h

end Lynth.Interval.Integral
