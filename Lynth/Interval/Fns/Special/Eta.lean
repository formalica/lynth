module

public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Data.Rat.Defs
public import Lynth.Interval.Core.Expr
public import Lynth.Analysis.SpecialFunctions
public import Lynth.Analysis.SpecialFunctionsDefs
public import Lynth.Interval.Core.Asy
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Fn
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Fns.ComplexElem
public import Lynth.Interval.Fns.Elem
public import Lynth.Interval.Fns.Special.Common
public import Lynth.Interval.Integral.Exp
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Series.Tail
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Fns.Special.Common

namespace Lynth.Interval.Fns

open SpecialFunctions Integral

@[expose] public def etaSumR (c : Ctx) (S : Ival) : List (ℕ × ℚ) → Ival
  | [] => Ival.zero
  | (k,w) :: ws => Ival.add c.prec
    (Ival.mul c.prec (Ival.ofRat c.prec w)
      (rpowIval c (Ival.ofRat c.prec k) (Ival.neg S))) (etaSumR c S ws)

theorem mem_etaSumR {c : Ctx} (hc : c.Valid) {s : ℝ} {S : Ival} (hs : s ∈ S)
    (ws : List (ℕ × ℚ)) :
    (ws.map fun (k,w) => (w : ℝ)*(k : ℝ)^(-s)).sum ∈ etaSumR c S ws := by
  induction ws with
  | nil => exact Ival.mem_zero
  | cons kw ws ih =>
    simpa only [etaSumR, List.map_cons, List.sum_cons, Rat.cast_natCast] using
      Ival.mem_add (Ival.mem_mul (Ival.mem_ofRat _ kw.2)
        (mem_rpowIval hc (Ival.mem_ofRat _ kw.1) (Ival.mem_neg hs))) ih

/-- Shift only the error estimate, never the value: this Euler transform
converges for all s and avoids cancellation of zeta's pole at one.
Keep Re(s)+m >= 1, including boxes close to a negative integer.
This prevents the complex Gamma-ratio estimate from becoming needlessly large. -/
@[expose] public def etaShift (lo : ℚ) : ℕ := (max 0 (1-lo).ceil).toNat

@[expose] public def etaRParams (c : Ctx) (lo : ℚ) : ℕ × ℕ :=
  let m := etaShift lo
  (m,c.prec+32+8*m*m)

@[expose] public def etaIval (c : Ctx) (S : Ival) : Ival :=
  match S.lo with
  | some lo =>
    let m := (etaRParams c lo.toRat).1
    let n := (etaRParams c lo.toRat).2
    if 0 < lo.toRat + m ∧ 4*m ≤ n ∧ n ≤ 4096 then
      specialWiden c.prec (etaSumR c S (etaWeights n))
        (Ival.ofRat c.prec (2*(n+1 : ℚ)^m / 2^n))
    else Ival.top
  | none => Ival.top

theorem mem_etaIval {c : Ctx} (hc : c.Valid) {s : ℝ} {S : Ival} (hs : s ∈ S) :
    Real.dirichletEta s ∈ etaIval c S := by
  unfold etaIval
  split
  · rename_i lo hlo
    dsimp only
    split
    · rename_i h
      have hp : (0 : ℝ) < s + (etaRParams c lo.toRat).1 := by
        have hh := hs.1 lo hlo
        have hl : (0 : ℝ) < lo.toReal + (etaRParams c lo.toRat).1 := by
          rw [Dy.toReal_def]
          exact_mod_cast h.1
        linarith
      apply mem_specialWiden (mem_etaSumR hc hs _) (Ival.mem_ofRat _ _)
      simpa only [etaApproxR, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat,
        Rat.cast_add, Rat.cast_natCast, Rat.cast_one] using eta_euler_error_real s _ _ hp h.2.1
    · exact Ival.mem_top _
  · exact Ival.mem_top _

@[expose] public def etaSumC (c : Ctx) (S : CBox) : List (ℕ × ℚ) → CBox
  | [] => CBox.ofReal Ival.zero
  | (k,w) :: ws => CBox.add c.prec
    (CBox.mul c.prec (CBox.ofReal (Ival.ofRat c.prec w))
      (cpowC.ev c (CBox.ofReal (Ival.ofRat c.prec k)) (CBox.neg S))) (etaSumC c S ws)

theorem mem_etaSumC {c : Ctx} (hc : c.Valid) {s : ℂ} {S : CBox} (hs : s ∈ S)
    (ws : List (ℕ × ℚ)) :
    (ws.map fun (k,w) => (w : ℂ)*(k : ℂ)^(-s)).sum ∈ etaSumC c S ws := by
  induction ws with
  | nil => simpa [etaSumC] using CBox.mem_ofReal Ival.mem_zero
  | cons kw ws ih =>
    have hp := cpowC.sound c (kw.1 : ℂ) (-s) _ _ _ hc rfl
      (CBox.mem_ofReal (Ival.mem_ofRat c.prec kw.1)) (CBox.mem_neg hs)
    simpa only [etaSumC, List.map_cons, List.sum_cons, Complex.ofReal_ratCast] using
      CBox.mem_add (CBox.mem_mul (CBox.mem_ofReal (Ival.mem_ofRat _ kw.2)) hp) ih

@[expose] public def etaCParams (c : Ctx) (lo : ℚ) (t : ℚ) : ℕ × ℕ :=
  let m := etaShift lo
  let a := lo+m
  let growth := (t^2/2 * (a⁻¹^2+a⁻¹)).ceil.toNat
  (m,c.prec+32+8*m*m+2*growth)

@[expose] public def etaCError (c : Ctx) (S : CBox) (m n : ℕ) : Ival :=
  let A := Ival.add c.prec S.re (Ival.ofRat c.prec m)
  let Ainv := Ival.inv c.prec A
  let exponent := Ival.mul c.prec (Ival.divNat c.prec (Ival.sq c.prec S.im) 2)
    (Ival.add c.prec (Ival.sq c.prec Ainv) Ainv)
  Ival.mul c.prec (Ival.ofRat c.prec (2*(n+1 : ℚ)^m / 2^n)) (fastExpIval c exponent)

theorem mem_etaCError (c : Ctx) {s : ℂ} {S : CBox} (hs : s ∈ S) (m n : ℕ) :
    2 * Real.exp (s.im^2/2 * ((s.re+m)⁻¹^2+(s.re+m)⁻¹)) * (n+1 : ℝ)^m / 2^n ∈
      etaCError c S m n := by
  unfold etaCError
  have hA := Ival.mem_inv (p := c.prec) (Ival.mem_add (p := c.prec) hs.1 (Ival.mem_ofRat c.prec m))
  have hE := mem_fastExpIval c (Ival.mem_mul (p := c.prec)
    (Ival.mem_divNat (p := c.prec) (Ival.mem_sq (p := c.prec) hs.2) (n := 2) (by omega))
    (Ival.mem_add (p := c.prec) (Ival.mem_sq (p := c.prec) hA) hA))
  have h := Ival.mem_mul (p := c.prec) (Ival.mem_ofRat c.prec (2*(n+1 : ℚ)^m / 2^n)) hE
  convert h using 1 <;> push_cast <;> ring

@[expose] public def etaCBox (c : Ctx) (S : CBox) : CBox :=
  match S.re.lo, (Ival.abs S.im).hi with
  | some lo, some t =>
    let m := (etaCParams c lo.toRat t.toRat).1
    let n := (etaCParams c lo.toRat t.toRat).2
    if 0 < lo.toRat + m ∧ 4*m ≤ n ∧ n ≤ 4096 then
      specialWidenC c.prec (etaSumC c S (etaWeights n)) (etaCError c S m n)
    else CBox.top
  | _, _ => CBox.top

theorem mem_etaCBox {c : Ctx} (hc : c.Valid) {s : ℂ} {S : CBox} (hs : s ∈ S) :
    Complex.dirichletEta s ∈ etaCBox c S := by
  unfold etaCBox
  split
  · rename_i lo t hlo _
    dsimp only
    split
    · rename_i h
      have hp : (0 : ℝ) < s.re + (etaCParams c lo.toRat t.toRat).1 := by
        have hh := hs.1.1 lo hlo
        have hl : (0 : ℝ) < lo.toReal + (etaCParams c lo.toRat t.toRat).1 := by
          rw [Dy.toReal_def]
          exact_mod_cast h.1
        linarith
      exact mem_specialWidenC (mem_etaSumC hc hs _) (mem_etaCError c hs _ _)
        (eta_euler_error s _ _ hp h.2.1)
    · exact CBox.mem_top _
  · exact CBox.mem_top _

@[expose, lynth_cfn] public def etaR : Fn1 .real .real where
  name := "dirichletEta"
  graph x y := y = Real.dirichletEta x
  exu := by exact exu_eq _
  ev := etaIval
  sound := fun _ _ _ _ hc hy hx => by cases hy; exact mem_etaIval hc hx
  cost := 500000

@[expose, lynth_cfn] public def etaC : Fn1 .cplx .cplx where
  name := "dirichletEta"
  graph x y := y = Complex.dirichletEta x
  exu := by exact exu_eq _
  ev := etaCBox
  sound := fun _ _ _ _ hc hy hx => by cases hy; exact mem_etaCBox hc hx
  cost := 1000000

end Lynth.Interval.Fns
