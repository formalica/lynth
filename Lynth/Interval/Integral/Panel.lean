module

public import Init.Control.Basic
public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.List.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Option.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Fns.Floor
public import Lynth.Interval.Fns.Trig
public import Lynth.Interval.Integral.Endpoint
public import Lynth.Interval.Integral.Eval
public import Lynth.Interval.Integral.Legendre
public import Lynth.Interval.Integral.Magnitude
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Integral.Memo
public import Lynth.Interval.Num.CBox
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Integral.LegendrePointProof
import all Lynth.Interval.Integral.Math.GaussError
import all Lynth.Interval.Integral.Math.IntegralBounds
import all Lynth.Interval.Integral.Math.Legendre
import all Lynth.Interval.Integral.Bounds
import all Lynth.Interval.Integral.Magnitude
import all Lynth.Interval.Integral.Endpoint
import all Lynth.Interval.Integral.Memo

/-! Certified direct and analytic Gauss-Legendre panels. -/

namespace Lynth.Interval.Integral

open Intgrl Fns

@[expose] public def specialize (c : Ctx) (X : Ival) : Term → Option Term
  | .unary .inv (.unary .cosh a) => do
    let A ← specialize c X a
    let V := evalR c A X
    -- Choose the decaying exponential to bound distant narrow peaks without
    -- cancellation in a rectangular complex enclosure of cosh.
    if V.nonneg || V.nonpos then
      let z := if V.nonneg then .unary .neg A else A
      let E := Term.unary .exp z
      return .binary .div (.binary .mul (.rat 2) E)
        (.binary .add (.rat 1) (.pow E 2))
    else return .unary .inv (.unary .cosh A)
  | .unary .floor .var =>
    match X.lo, X.hi with
    | some a, some b =>
      let k := Dy.floor a
      if Dy.leB b (Dy.ofInt (k+1)) then some (.rat k) else none
    | _, _ => none
  | .unary op a => do
    let A ← specialize c X a
    match op with
    | .abs =>
      let V := evalR c A X
      if V.nonneg then some A else if V.nonpos then some (.unary .neg A) else none
    | .floor =>
      let V := intFloorIval (evalR c A X)
      match V.lo, V.hi with
      | some a, some b => if a.toRat == b.toRat then some (.rat a.toRat) else none
      | _, _ => none
    | .log =>
      if (evalR c A X).negv then some (.unary .log (.unary .neg A)) else some (.unary .log A)
    | .sqrt => if (evalR c A X).nonpos then some (.rat 0) else some (.unary .sqrt A)
    | _ => some (.unary op A)
  | .binary op a b => do
    let A ← specialize c X a
    let B ← specialize c X b
    match op with
    | .max =>
      let VA := evalR c A X
      let VB := evalR c B X
      if Ival.leB VA VB then some B else if Ival.leB VB VA then some A else none
    | .min =>
      let VA := evalR c A X
      let VB := evalR c B X
      if Ival.leB VA VB then some A else if Ival.leB VB VA then some B else none
    | _ => some (.binary op A B)
  | .pow a n => do return .pow (← specialize c X a) n
  | .rpow a q => do return .rpow (← specialize c X a) q
  | e => some e

theorem specialize_sound {c : Ctx} (hc : c.Valid) {X : Ival} {e a : Term}
    (h : specialize c X e = some a) {x : ℝ} (hx : x ∈ X)
    (hinterior : ∀ lo hi, X.lo = some lo → X.hi = some hi →
      lo.toReal < x ∧ x < hi.toReal) :
    a.real x = e.real x := by
  have hnonpos : ∀ {I : Ival} {v : ℝ}, I.nonpos = true → v ∈ I → v ≤ 0 := by
    intro I v hi hv
    have hh := Ival.nonneg_of (Ival.neg_nonneg_of_nonpos hi) (Ival.mem_neg hv)
    linarith
  have hsech : ∀ t : ℝ, 2*Real.exp t/(1+Real.exp t^2) = (Real.cosh t)⁻¹ := by
    intro t
    rw [Real.cosh_eq, Real.exp_neg]
    have he := Real.exp_pos t
    have hden : 1 + Real.exp t ^ 2 ≠ 0 := by positivity
    field_simp
    <;> ring
  fun_induction specialize c X e generalizing a with
  | case1 e ih =>
    cases hs : specialize c X e with
    | none => simp [hs] at h
    | some A =>
      simp only [hs, bind, Option.bind] at h
      split at h
      · cases hn : (evalR c A X).nonneg <;>
          simp only [hn, Bool.false_eq_true, ↓reduceIte, pure, Option.some.injEq] at h <;>
          subst a <;>
          simp only [Term.real, Unary.real, Binary.real, Rat.cast_ofNat, Rat.cast_one] <;>
          rw [hsech] <;> simp only [Real.cosh_neg, ih hs]
      · have ha := Option.some.inj h
        subst a
        simp only [Term.real, Unary.real, ih hs]
  | case2 lo hi hhi hlo k hle =>
    have hl : (k : ℝ) ≤ lo.toReal := by
      change ((Dy.floor lo : ℤ) : ℝ) ≤ (lo.toRat : ℝ)
      exact_mod_cast Dy.floor_le_toRat lo
    have hu : hi.toReal ≤ (k : ℝ)+1 := by
      simpa [Dy.toReal_def] using Dy.toReal_le_of_leB hle
    have hx' := hinterior lo hi hlo hhi
    have hf : ⌊x⌋ = k := Int.floor_eq_iff.mpr ⟨hl.trans hx'.1.le,hx'.2.trans_le hu⟩
    cases Option.some.inj h
    simp only [Term.real, Unary.real, hf, Rat.cast_intCast]
  | case3 => simp at h
  | case4 => simp at h
  | case5 op e _ _ ih =>
    cases hs : specialize c X e with
    | none => simp [hs] at h
    | some A =>
      simp only [hs, bind, Option.bind] at h
      have hv := evalR_sound hc A hx
      have he := ih hs
      cases op with
      | abs =>
        dsimp only at h
        split at h
        · rename_i hp
          cases Option.some.inj h
          simpa only [Term.real, Unary.real, ← he, abs_of_nonneg (Ival.nonneg_of hp hv)]
        · split at h
          · rename_i hn
            cases Option.some.inj h
            simpa only [Term.real, Unary.real, ← he, abs_of_nonpos (hnonpos hn hv)]
          · simp at h
      | floor =>
        dsimp only at h
        cases hlo : (intFloorIval (evalR c A X)).lo with
        | none => simp [hlo] at h
        | some lo =>
          cases hhi : (intFloorIval (evalR c A X)).hi with
          | none => simp [hlo,hhi] at h
          | some hi =>
            simp only [hlo,hhi] at h
            split at h
            · rename_i heq
              have hlh : lo.toRat = hi.toRat := by simpa using heq
              have hf := mem_intFloor hv
              have hval : (⌊A.real x⌋ : ℝ) = lo.toReal := le_antisymm
                (by simpa only [Dy.toReal_def, ← hlh] using hf.2 hi hhi) (hf.1 lo hlo)
              cases Option.some.inj h
              simpa only [Term.real, Unary.real, ← he, hval, Dy.toReal_def]
            · simp at h
      | log =>
        dsimp only at h
        split at h <;> cases Option.some.inj h <;>
          simp only [Term.real, Unary.real, Real.log_neg_eq_log, he]
      | sqrt =>
        dsimp only at h
        split at h
        · rename_i hn
          cases Option.some.inj h
          simp only [Term.real, Unary.real, ← he, Real.sqrt_eq_zero_of_nonpos (hnonpos hn hv),
            Rat.cast_zero]
        · cases Option.some.inj h
          simp only [Term.real, Unary.real, he]
      | neg | inv | exp | sin | cos | sinh | cosh | atan | erf | si | eta | airyAi =>
        cases Option.some.inj h
        simp only [Term.real, he]
  | case6 op e f ihe ihf =>
    cases hs : specialize c X e with
    | none => simp [hs] at h
    | some A =>
      cases ht : specialize c X f with
      | none => simp [hs,ht] at h
      | some B =>
        simp only [hs,ht,bind,Option.bind] at h
        have ha := ihe hs
        have hb := ihf ht
        have hva := evalR_sound hc A hx
        have hvb := evalR_sound hc B hx
        cases op with
        | max =>
          dsimp only at h
          split at h
          · rename_i hle
            cases Option.some.inj h
            simpa only [Term.real, Binary.real, ← ha, ← hb,
              max_eq_right (Ival.le_of_leB hva hvb hle)]
          · split at h
            · rename_i hle
              cases Option.some.inj h
              simpa only [Term.real, Binary.real, ← ha, ← hb,
                max_eq_left (Ival.le_of_leB hvb hva hle)]
            · simp at h
        | min =>
          dsimp only at h
          split at h
          · rename_i hle
            cases Option.some.inj h
            simpa only [Term.real, Binary.real, ← ha, ← hb,
              min_eq_left (Ival.le_of_leB hva hvb hle)]
          · split at h
            · rename_i hle
              cases Option.some.inj h
              simpa only [Term.real, Binary.real, ← ha, ← hb,
                min_eq_right (Ival.le_of_leB hvb hva hle)]
            · simp at h
        | add | sub | mul | div =>
          cases Option.some.inj h
          simp only [Term.real, ha, hb]
  | case7 e n ih =>
    cases hs : specialize c X e with
    | none => simp [hs] at h
    | some A =>
      have he : A.pow n = a := by simpa [hs] using h
      subst a
      simp only [Term.real, ih hs]
  | case8 e q ih =>
    cases hs : specialize c X e with
    | none => simp [hs] at h
    | some A =>
      have he : A.rpow q = a := by simpa [hs] using h
      subst a
      simp only [Term.real, ih hs]
  | case9 => cases Option.some.inj h; rfl

theorem pointPair_sound {c : Ctx} (hc : c.Valid) (n : ℕ) {x : Dy}
    (hx : |x.toReal| < 1) :
    (legendre n).eval x.toReal ∈ (pointPair c n x).1 ∧
      (legendre n).derivative.eval x.toReal ∈ (pointPair c n x).2 := by
  exact pointPair_sound_impl hc n hx

theorem onInterval_sound {c : Ctx} (hc : c.Valid) (n : ℕ) {X : Ival}
    {x : ℝ} (hx : x ∈ X)
    (hX : ∀ y : ℝ, y ∈ X → |y| < 1) :
    (legendre n).eval x ∈ (onInterval c n X).1 ∧
      (legendre n).derivative.eval x ∈ (onInterval c n X).2 := by
  unfold onInterval
  split
  · rename_i _ _ _ m a b hm ha hb
    have he : Vendor.Dyadic.scale2 (a.add b) (-1) = m := by
      simpa only [Ival.mid,ha,hb,Ival.omap2,Option.some.injEq] using hm
    have hmr : m.toReal = (a.toReal+b.toReal)/2 := by
      rw [← he]
      simp only [Dy.toReal_def,Vendor.Dyadic.toRat_scale2,Dy.toRat_add']
      norm_num
      ring
    have ham : a.toReal ≤ m.toReal := by
      rw [hmr]
      linarith [hx.1 a ha,hx.2 b hb]
    have hmb : m.toReal ≤ b.toReal := by
      rw [hmr]
      linarith [hx.1 a ha,hx.2 b hb]
    have hmX : m.toReal ∈ X := by
      constructor
      · intro l hl
        have hl' : l = a := Option.some.inj (hl.symm.trans ha)
        exact hl' ▸ ham
      · intro u hu
        have hu' : u = b := Option.some.inj (hu.symm.trans hb)
        exact hu' ▸ hmb
    let radius := Dy.max (Dy.subU c.prec m a) (Dy.subU c.prec b m)
    have hra : m.toReal-a.toReal ≤ radius.toReal := by
      apply le_trans _ (Ival.le_max_toReal_left _ _)
      change (m.toRat:ℝ)-(a.toRat:ℝ) ≤ ((Dy.subU c.prec m a).toRat:ℝ)
      exact_mod_cast Dy.le_subU c.prec m a
    have hrb : b.toReal-m.toReal ≤ radius.toReal := by
      apply le_trans _ (Ival.le_max_toReal_right _ _)
      change (b.toRat:ℝ)-(m.toRat:ℝ) ≤ ((Dy.subU c.prec b m).toRat:ℝ)
      exact_mod_cast Dy.le_subU c.prec b m
    have hradius : ∀ y ∈ X, |y-m.toReal| ≤ radius.toReal := by
      intro y hy
      apply abs_le.mpr
      constructor <;> linarith [hy.1 a ha,hy.2 b hb]
    have hr0 : 0 ≤ radius.toReal := by simpa using hradius m.toReal hmX
    rcases hpair : pointPair c n m with ⟨v₀,d₀⟩
    have hcenter := pointPair_sound hc n (hX m.toReal hmX)
    rw [hpair] at hcenter
    let E := Ival.mul c.prec (secondBound c.prec n X) (Ival.pt radius)
    let D : Ival := match E.hi with
      | some err => Ival.widen c.prec d₀ err
      | none => Ival.top
    have hderiv : ∀ y ∈ X, (legendre n).derivative.eval y ∈ D := by
      intro y hy
      cases hE : E.hi with
      | none => simpa only [D,hE] using Ival.mem_top ((legendre n).derivative.eval y)
      | some err =>
        have herr : ∀ z ∈ X,
            |(legendre n).derivative.derivative.eval z| *radius.toReal ≤ err.toReal := by
          intro z hz
          obtain ⟨B,hB,_,hbound⟩ := secondBound_sound (p := c.prec) hz (hX z hz)
          exact (mul_le_mul_of_nonneg_right hbound hr0).trans
            ((Ival.mem_mul (p := c.prec) hB (Ival.mem_pt radius)).2 err hE)
        obtain ⟨z,hz,hdiff⟩ := polynomial_difference (legendre n).derivative m.toReal y
        have hzX := ival_segment_mem hmX hy hz
        have hbound : |(legendre n).derivative.eval y-(legendre n).derivative.eval m.toReal| ≤
            err.toReal := by
          rw [hdiff,abs_mul]
          exact (mul_le_mul_of_nonneg_right (hradius y hy) (abs_nonneg _)).trans
            (by simpa only [mul_comm] using herr z hzX)
        simpa only [D,hE] using Ival.mem_widen hcenter.2 hbound
    let F := Ival.mul c.prec (Ival.abs D) (Ival.pt radius)
    change (legendre n).eval x ∈
      (match F.hi with | some err => Ival.widen c.prec v₀ err | none => Ival.top) ∧
      (legendre n).derivative.eval x ∈ D
    refine ⟨?_,hderiv x hx⟩
    cases hF : F.hi with
    | none => simpa only [hF] using Ival.mem_top ((legendre n).eval x)
    | some err =>
      have herr : ∀ z ∈ X, |(legendre n).derivative.eval z| *radius.toReal ≤ err.toReal := by
        intro z hz
        exact (Ival.mem_mul (p := c.prec) (Ival.mem_abs (hderiv z hz))
          (Ival.mem_pt radius)).2 err hF
      obtain ⟨z,hz,hdiff⟩ := polynomial_difference (legendre n) m.toReal x
      have hbound : |(legendre n).eval x-(legendre n).eval m.toReal| ≤ err.toReal := by
        rw [hdiff,abs_mul]
        exact (mul_le_mul_of_nonneg_right (hradius x hx) (abs_nonneg _)).trans
          (by simpa only [mul_comm] using herr z (ival_segment_mem hmX hx hz))
      simpa only [hF] using Ival.mem_widen hcenter.1 hbound
  · exact ⟨Ival.mem_top _,Ival.mem_top _⟩

theorem gaussWeightI_sound {c : Ctx} (hc : c.Valid) (n : Nat) {X : Ival} {x : ℝ}
    (hx : x ∈ X) (hX : ∀ y ∈ X, |y| < 1) : gaussWeight n x ∈ gaussWeightI c n X := by
  have hd := (onInterval_sound hc n hx hX).2
  exact Ival.mem_div (Ival.mem_ofRat c.prec 2)
    (Ival.mem_mul (Ival.mem_sub Ival.mem_one (Ival.mem_sq hx)) (Ival.mem_sq hd))

theorem gaussWeight_neg (n : Nat) (x : ℝ) : gaussWeight n (-x) = gaussWeight n x := by
  have h₁ : HasDerivAt (fun y : ℝ => (legendre n).eval (-y))
      (-(legendre n).derivative.eval (-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using
      ((legendre n).hasDerivAt (-x)).comp x ((hasDerivAt_id x).neg)
  have h₂ : HasDerivAt (fun y : ℝ => (legendre n).eval (-y))
      ((-1:ℝ)^n*(legendre n).derivative.eval x) x := by
    simpa only [legendre_parity] using ((legendre n).hasDerivAt x).const_mul ((-1:ℝ)^n)
  have he := h₁.unique h₂
  have hs : (legendre n).derivative.eval (-x)^2 = (legendre n).derivative.eval x^2 := by
    have hd : (legendre n).derivative.eval (-x) = -((-1:ℝ)^n*(legendre n).derivative.eval x) := by
      linarith
    rw [hd,neg_sq,mul_pow,← pow_mul, Nat.mul_comm n 2,pow_mul]
    simp
  simp only [gaussWeight,neg_sq,hs]

theorem rawDyEq_sound {a b : Dy} (h : rawDyEq a b = true) : a = b := by
  rcases a with ⟨am,ae⟩
  rcases b with ⟨bm,be⟩
  have hh : am = bm ∧ ae = be := by simpa [rawDyEq] using h
  rcases hh with ⟨rfl,rfl⟩
  rfl

theorem rawEndpointEq_sound {a b : Option Dy} (h : rawEndpointEq a b = true) : a = b := by
  cases a with
  | none => cases b <;> simp_all [rawEndpointEq]
  | some a =>
    cases b with
    | none => simp [rawEndpointEq] at h
    | some b => exact congrArg some (rawDyEq_sound h)

theorem rawIvalEq_sound {a b : Ival} (h : rawIvalEq a b = true) : a = b := by
  obtain ⟨hl,hu⟩ := Bool.and_eq_true_iff.mp h
  have hl' := rawEndpointEq_sound hl
  have hu' := rawEndpointEq_sound hu
  cases a
  cases b
  dsimp only at hl' hu'
  cases hl'
  cases hu'
  rfl

/-- Semantic root brackets, including the reflected half of a symmetric table. -/
def RootBracket (n : Nat) (r : Dy × Dy) : Prop :=
  (∀ y ∈ rootIval r, |y| < 1) ∧ ∃ y ∈ rootIval r, (legendre n).eval y = 0

theorem rootSignCheck_sound {c : Ctx} (hc : c.Valid) {n : Nat} {r : Dy × Dy}
    (h : rootSignCheck c n r = true) : RootBracket n r := by
  have hh : Dy.ltB r.1 r.2 = true ∧ Dy.ltB (Dy.ofInt (-1)) r.1 = true ∧
      Dy.ltB r.2 Dy.one = true ∧
      (Ival.mul c.prec (pointPair c n r.1).1 (pointPair c n r.2).1).negv = true := by
    simpa only [rootSignCheck,Bool.and_eq_true,and_assoc] using h
  obtain ⟨hab,hlo,hhi,hneg⟩ := hh
  have hab' := Dy.toReal_lt_of_ltB hab
  have hlo' : -1 < r.1.toReal := by simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB hlo
  have hhi' : r.2.toReal < 1 := by simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB hhi
  have hX : ∀ y ∈ rootIval r, |y| < 1 := by
    intro y hy
    exact abs_lt.mpr ⟨hlo'.trans_le (hy.1 r.1 rfl),(hy.2 r.2 rfl).trans_lt hhi'⟩
  have ha : r.1.toReal ∈ rootIval r := ⟨by simp [Ival.LoLe,rootIval],by
    simpa [Ival.LeHi,rootIval] using hab'.le⟩
  have hb : r.2.toReal ∈ rootIval r := ⟨by
    simpa [Ival.LoLe,rootIval] using hab'.le,by simp [Ival.LeHi,rootIval]⟩
  have hp : (legendre n).eval r.1.toReal*(legendre n).eval r.2.toReal < 0 :=
    Ival.neg_of hneg (Ival.mem_mul (pointPair_sound hc n (hX _ ha)).1
      (pointPair_sound hc n (hX _ hb)).1)
  refine ⟨hX,?_⟩
  rcases mul_neg_iff.mp hp with ⟨hpa,hpb⟩ | ⟨hpa,hpb⟩
  · obtain ⟨y,hy,he⟩ := intermediate_value_Icc' hab'.le
      (legendre n).continuous.continuousOn ⟨hpb.le,hpa.le⟩
    exact ⟨y,by simpa [rootIval] using hy,he⟩
  · obtain ⟨y,hy,he⟩ := intermediate_value_Icc hab'.le
      (legendre n).continuous.continuousOn ⟨hpa.le,hpb.le⟩
    exact ⟨y,by simpa [rootIval] using hy,he⟩

def reflectRoot (r : Dy × Dy) : Dy × Dy := (r.2.neg,r.1.neg)

theorem reflectRoot_mem {r : Dy × Dy} {x : ℝ} (hx : x ∈ rootIval (reflectRoot r)) :
    -x ∈ rootIval r := by
  constructor
  · intro l hl
    have he : r.1 = l := Option.some.inj hl
    subst l
    have hh := hx.2 r.1.neg rfl
    simp only [Dy.toReal_def,Dy.toRat_neg',Rat.cast_neg] at hh ⊢
    linarith
  · intro u hu
    have he : r.2 = u := Option.some.inj hu
    subst u
    have hh := hx.1 r.2.neg rfl
    simp only [Dy.toReal_def,Dy.toRat_neg',Rat.cast_neg] at hh ⊢
    linarith

theorem reflectRoot_mem_neg {r : Dy × Dy} {x : ℝ} (hx : x ∈ rootIval r) :
    -x ∈ rootIval (reflectRoot r) := by
  constructor
  · intro l hl
    have he : r.2.neg = l := Option.some.inj hl
    subst l
    have hh := hx.2 r.2 rfl
    simpa only [Dy.toReal_def,Dy.toRat_neg',Rat.cast_neg,neg_le_neg_iff] using hh
  · intro u hu
    have he : r.1.neg = u := Option.some.inj hu
    subst u
    have hh := hx.1 r.1 rfl
    simpa only [Dy.toReal_def,Dy.toRat_neg',Rat.cast_neg,neg_le_neg_iff] using hh

theorem RootBracket.reflect {n : Nat} {r : Dy × Dy} (h : RootBracket n r) :
    RootBracket n (reflectRoot r) := by
  refine ⟨fun y hy => by simpa only [abs_neg] using h.1 (-y) (reflectRoot_mem hy),?_⟩
  obtain ⟨y,hy,hzero⟩ := h.2
  exact ⟨-y,reflectRoot_mem_neg hy,by rw [legendre_parity,hzero,mul_zero]⟩

theorem list_eq_of_zip_all {α : Type} {f : α → α → Bool}
    (hf : ∀ a b, f a b = true → a = b) {xs ys : List α}
    (hlen : xs.length = ys.length) (h : (xs.zip ys).all (fun (a,b) => f a b) = true) :
    xs = ys := by
  have hh : List.Forall₂ (fun a b => a = b) xs ys :=
    List.forall₂_iff_zip.mpr ⟨hlen,fun hab => hf _ _ (List.all_eq_true.mp h _ hab)⟩
  simpa only [List.forall₂_eq_eq_eq] using hh

theorem NodeTable.data {c : Ctx} (hc : c.Valid) (t : NodeTable) (h : t.check c = true) :
    List.Forall₂ (fun r w => RootBracket t.roots.length r ∧
      ∀ y ∈ rootIval r, gaussWeight t.roots.length y ∈ w) t.roots (t.computeWeights c) ∧
    (t.roots.zip t.roots.tail).all (fun (a,b) => Dy.ltB a.2 b.1) = true := by
  have hroots := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1
  by_cases hone : t.roots.length = 1
  · obtain ⟨r,hr⟩ := List.length_eq_one_iff.mp hone
    obtain ⟨a,b⟩ := r
    have hab : a.isZero = true ∧ b.isZero = true := by
      simpa [NodeTable.check,hone,hr] using hroots
    have ha : a.toReal = 0 := by
      have hma : a.mantissa = 0 := by simpa [Dy.isZero] using hab.1
      simp [Dy.toReal_def,Vendor.Dyadic.toRat_eq,hma]
    have hb : b.toReal = 0 := by
      have hmb : b.mantissa = 0 := by simpa [Dy.isZero] using hab.2
      simp [Dy.toReal_def,Vendor.Dyadic.toRat_eq,hmb]
    have hz : (0:ℝ) ∈ rootIval (a,b) := by simp [rootIval,ha,hb]
    have hy : ∀ y ∈ rootIval (a,b), y = 0 := by
      intro y hy
      exact le_antisymm (by simpa [hb] using hy.2 b rfl) (by simpa [ha] using hy.1 a rfl)
    constructor
    · simp only [NodeTable.computeWeights,hone,beq_self_eq_true,↓reduceIte,hr]
      refine .cons ⟨⟨fun y h => by rw [hy y h]; norm_num,
        ⟨0,hz,by simp [legendre]⟩⟩,?_⟩ .nil
      intro y h
      rw [hy y h]
      simpa [gaussWeight,legendre] using Ival.mem_ofRat c.prec 2
    · simp [hr]
  · let right := t.roots.drop (t.roots.length/2)
    have hh : 0 < t.roots.length ∧ t.roots.length%2 = 0 ∧
        ((t.roots.take (t.roots.length/2)).zip (reflectedRoots right)).all
          (fun (a,b) => rawDyEq a.1 b.1 && rawDyEq a.2 b.2) = true ∧
        right.all (rootSignCheck c t.roots.length) = true ∧
        (t.roots.zip t.roots.tail).all (fun (a,b) => Dy.ltB a.2 b.1) = true := by
      simpa only [NodeTable.check,hone,beq_iff_eq,↓reduceIte,Bool.and_eq_true,
        decide_eq_true_eq,and_assoc,right] using hroots
    obtain ⟨hN,heven,hsym,hright,hsort⟩ := hh
    have hlen : (t.roots.take (t.roots.length/2)).length = (reflectedRoots right).length := by
      simp [reflectedRoots,right]
      omega
    have hleft : t.roots.take (t.roots.length/2) = reflectedRoots right :=
      list_eq_of_zip_all (fun a b h => Prod.ext
        (rawDyEq_sound (Bool.and_eq_true_iff.mp h).1)
        (rawDyEq_sound (Bool.and_eq_true_iff.mp h).2)) hlen hsym
    let R := fun (r : Dy × Dy) (w : Ival) => RootBracket t.roots.length r ∧
      ∀ y ∈ rootIval r, gaussWeight t.roots.length y ∈ w
    have hp : List.Forall₂ R right (right.map (fun r => gaussWeightI c t.roots.length (rootIval r))) := by
      apply List.forall₂_of_length_eq_of_get (by simp)
      intro i hi hj
      have hbr := rootSignCheck_sound hc ((List.all_eq_true.mp hright) _ (List.getElem_mem hi))
      refine ⟨hbr,?_⟩
      intro y hy
      simpa using gaussWeightI_sound hc t.roots.length hy hbr.1
    have hn : List.Forall₂ R (reflectedRoots right)
        ((right.map (fun r => gaussWeightI c t.roots.length (rootIval r))).reverse) := by
      have hs := (List.rel_reverse hp).imp (fun r w (hrw : R r w) =>
        (show R (reflectRoot r) w from ⟨hrw.1.reflect,fun y hy => by
          simpa only [gaussWeight_neg] using hrw.2 (-y) (reflectRoot_mem hy)⟩))
      simpa only [reflectedRoots,reflectRoot,List.forall₂_map_left_iff] using hs
    constructor
    · have he : t.roots = reflectedRoots right ++ right := by
        rw [← hleft]
        exact (List.take_append_drop (t.roots.length/2) t.roots).symm
      change List.Forall₂ R t.roots (t.computeWeights c)
      have hw : t.computeWeights c =
          (right.map (fun r => gaussWeightI c t.roots.length (rootIval r))).reverse ++
            right.map (fun r => gaussWeightI c t.roots.length (rootIval r)) := by
        simp only [NodeTable.computeWeights,hone,beq_iff_eq,↓reduceIte]
        rfl
      rw [hw,he]
      simpa only [he] using List.rel_append hn hp
    · exact hsort

/-- Table certification exposes only exact mathematical nodes and weights.
The remaining numeric bridge proofs stay here because they depend on Ival. -/
theorem NodeTable.sound {c : Ctx} (hc : c.Valid) (t : NodeTable)
    (h : t.check c = true) :
    ∃ x : Fin t.roots.length → ℝ,
      IsGaussNodes x ∧
      ∀ i, x i ∈ rootIval (t.roots[i]) ∧
        gaussWeight t.roots.length (x i) ∈ (t.weights c).getD i.val Ival.top := by
  classical
  obtain ⟨hdata,hsort⟩ := t.data hc h
  have hlen : (t.weights c).length = t.roots.length := by
    have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2
    simpa only [NodeTable.weights,beq_iff_eq] using hh
  have hw : t.computeWeights c = t.weights c := list_eq_of_zip_all
    (fun _ _ h => rawIvalEq_sound h) (hdata.length_eq.symm.trans hlen.symm)
    (Bool.and_eq_true_iff.mp h).2
  rw [hw] at hdata
  have hi : ∀ i : Fin t.roots.length, RootBracket t.roots.length t.roots[i] ∧
      ∀ y ∈ rootIval t.roots[i], gaussWeight t.roots.length y ∈ (t.weights c)[i.val] := by
    intro i
    exact hdata.get i.isLt (by simpa [hlen] using i.isLt)
  choose x hx hz using fun i => (hi i).1.2
  have hcchain : List.IsChain (fun (x y : ℝ) => x < y) (List.ofFn x) := by
    apply List.isChain_iff_getElem.mpr
    intro i hib
    have hib' : i+1 < t.roots.length := by simpa using hib
    have hia : i < t.roots.length := by omega
    have hzip : i < (t.roots.zip t.roots.tail).length := by simp; omega
    have hsep := (List.all_eq_true.mp hsort) _ (List.getElem_mem hzip)
    simp only [List.getElem_zip,List.getElem_tail] at hsep
    have hs := Dy.toReal_lt_of_ltB hsep
    have hlt : x ⟨i,hia⟩ < x ⟨i+1,hib'⟩ :=
      ((hx ⟨i,hia⟩).2 _ rfl).trans_lt (hs.trans_le ((hx ⟨i+1,hib'⟩).1 _ rfl))
    simpa using hlt
  have hstrict : StrictMono x :=
    List.pairwise_ofFn.mp (List.isChain_iff_pairwise.mp hcchain)
  refine ⟨x,⟨hstrict.injective,fun i => ⟨?_,hz i⟩⟩,fun i => ⟨hx i,?_⟩⟩
  · exact abs_lt.mp ((hi i).1.1 _ (hx i))
  · have hiw : i.val < (t.weights c).length := by rw [hlen]; exact i.isLt
    rw [List.getD_eq_getElem (t.weights c) Ival.top hiw]
    exact (hi i).2 _ (hx i)

@[expose] public def balancedSum (p : Nat) (xs : List Ival) : Ival :=
  let rec go : Nat → List Ival → Ival
    | 0, xs => xs.foldl (Ival.add p) Ival.zero
    | fuel + 1, xs =>
      if xs.length ≤ 4 then xs.foldl (Ival.add p) Ival.zero else
        let (a,b) := xs.splitAt (xs.length / 2)
        Ival.add p (go fuel a) (go fuel b)
  go 64 xs

theorem foldl_add_mem {p : Nat} {xs : List ℝ} {Is : List Ival}
    (h : List.Forall₂ (fun x I => x ∈ I) xs Is) {s : ℝ} {S : Ival} (hs : s ∈ S) :
    s + xs.sum ∈ Is.foldl (Ival.add p) S := by
  induction h generalizing s S with
  | nil => simpa using hs
  | cons hx _ ih => simpa [List.sum_cons, add_assoc] using ih (Ival.mem_add hs hx)

theorem balancedSum_mem {p : Nat} {xs : List ℝ} {Is : List Ival}
    (h : List.Forall₂ (fun x I => x ∈ I) xs Is) : xs.sum ∈ balancedSum p Is := by
  have hgo : ∀ fuel xs Is, List.Forall₂ (fun (x : ℝ) (I : Ival) => x ∈ I) xs Is →
      xs.sum ∈ balancedSum.go p fuel Is := by
    intro fuel
    induction fuel with
    | zero =>
      intro xs Is h
      simpa [balancedSum.go] using foldl_add_mem h Ival.mem_zero
    | succ fuel ih =>
      intro xs Is h
      simp only [balancedSum.go]
      split
      · simpa using foldl_add_mem h Ival.mem_zero
      · rw [List.splitAt_eq]
        simpa only [List.sum_take_add_sum_drop] using
          Ival.mem_add (ih _ _ (List.forall₂_take (Is.length/2) h))
            (ih _ _ (List.forall₂_drop (Is.length/2) h))
  exact hgo 64 xs Is h

@[expose] public def panelBox (a b : Dy) : Ival := ⟨some a, some b⟩

@[expose] public def directPanelSpecialized (c : Ctx) (ext : Term) (a b : Dy) : Option Ival :=
  let V := prepareEval c ext (panelBox a b)
  if V.isFinite then
    some (Ival.mul c.prec (Ival.ofRat c.prec (b.toRat - a.toRat)) V)
  else none

@[expose] public def directPanelCoarse (c : Ctx) (e : Term) (a b : Dy) : Option Ival :=
  directPanelSpecialized c ((specialize c (panelBox a b) e).getD e) a b

@[expose] public def directPanel (c : Ctx) (e : Term) (a b : Dy) : Option Ival :=
  (oscillatoryPanel c e a b).orElse fun _ => directPanelCoarse c e a b

@[expose] public def ellipseBox (c : Ctx) (a b ρ : Dy) : CBox :=
  let p := c.prec
  let r := ρ.toRat
  let x := (r + 1/r) / 2
  let y := (r - 1/r) / 2
  let mid := Ival.ofRat p ((a.toRat + b.toRat) / 2)
  let delta := Ival.ofRat p ((b.toRat - a.toRat) / 2)
  CBox.add p (CBox.ofReal mid)
    (CBox.mul p (CBox.ofReal delta)
      ⟨Ival.ofRats p (-x) x, Ival.ofRats p (-y) y⟩)

/-- Search uses binary ellipses. Exact binary scaling replaces repeated
interval exponentiation in their geometric remainder. Other ellipses keep
the general interval formula. -/
@[expose] public def binaryRho (ρ : Dy) : Option Nat :=
  if ρ.mantissa == 1 && 1 ≤ ρ.exponent && ρ.exponent ≤ 4 then
    some ρ.exponent.toNat else none

theorem binaryRho_sound {ρ : Dy} {k : Nat} (h : binaryRho ρ = some k) :
    0 < k ∧ ρ.toReal = (2 : ℝ)^k := by
  unfold binaryRho at h
  split at h
  · rename_i hk
    have hg : ρ.mantissa = 1 ∧ 1 ≤ ρ.exponent ∧ ρ.exponent ≤ 4 := by
      simpa only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] using hk
    have heq : ρ.exponent.toNat = k := Option.some.inj h
    have he : ρ.exponent = (k : Int) := by omega
    refine ⟨by omega, ?_⟩
    simp only [Dy.toReal_def, Vendor.Dyadic.toRat_eq ρ, hg.1, he]
    norm_cast
    simp
  · simp at h

@[expose] public def binaryErrorBase (c : Ctx) (a b M : Dy) (k : Nat) : Dy :=
  let numerator := Dy.scale2 ((b.add a.neg).mul M) 5
  Dy.divU c.prec numerator (Dy.ofNat (15 * (2^k-1)))

@[expose] public def binaryError (base : Dy) (k n : Nat) : Dy :=
  Dy.scale2 base (-((k * (2*n-1) : Nat) : Int))

@[expose] public def errorBound (c : Ctx) (n : Nat) (a b ρ : Dy) (M : Dy) : Option Dy :=
  if let some k := binaryRho ρ then
    some (binaryError (binaryErrorBase c a b M k) k n)
  else
  let p := c.prec
  let r := Ival.pt ρ
  let num := Ival.mul p (Ival.ofRat p 64)
    (Ival.mul p (Ival.ofRat p ((b.toRat - a.toRat)/2)) (Ival.pt M))
  let den := Ival.mul p (Ival.ofRat p 15)
    (Ival.mul p (Ival.sub p r Ival.one) (Ival.npow p r (2*n-1)))
  (Ival.div p num den).hi

/-- Range check for an already selected real branch. Search shares this
branch across ellipse trials; certificate replay selects it independently. -/
@[expose] public def analyticBoundSpecialized (c : Ctx) (ext : Term) (a b ρ : Dy) : Option Dy := do
  if !(Dy.ltB Dy.one ρ) then none else do
    let Z := ellipseBox c a b ρ
    if !regularCheck c ext Z then none else
      analyticMagnitude c ext Z

/-- Analytic test and remainder do not evaluate any quadrature nodes. -/
@[expose] public def analyticBound (c : Ctx) (e : Term) (a b ρ : Dy) : Option Dy := do
  let ext ← specialize c (panelBox a b) e
  analyticBoundSpecialized c ext a b ρ

@[expose] public def gaussSamples (c : Ctx) (e : Term) (a b : Dy)
    (t : NodeTable) (weights : List Ival) : Ival :=
  let p := c.prec
  let mid := Ival.ofRat p ((a.toRat+b.toRat)/2)
  let delta := Ival.ofRat p ((b.toRat-a.toRat)/2)
  let evaluate := prepareEval c e
  let vals := (t.roots.zip weights).map fun (r,w) =>
    mulSigned p w (evaluate (Ival.add p mid (Ival.mul p delta (rootIval r))))
  mulSigned p delta (balancedSum p vals)

@[expose] public def gaussPanel (c : Ctx) (e : Term) (a b ρ : Dy)
    (t : NodeTable) (weights : List Ival) : Option Ival := do
  let M ← analyticBound c e a b ρ
  let err ← errorBound c t.roots.length a b ρ M
  return Ival.widen c.prec (gaussSamples c e a b t weights) err

theorem directPanelCoarse_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b : Dy}
    (hab : a.toReal ≤ b.toReal) {I : Ival}
    (h : directPanelCoarse c e a b = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  let ext := (specialize c (panelBox a b) e).getD e
  let V := prepareEval c ext (panelBox a b)
  change (if V.isFinite then
    some (Ival.mul c.prec (Ival.ofRat c.prec (b.toRat-a.toRat)) V)
    else none) = some I at h
  split at h
  · rename_i hfinite
    have hL : b.toReal - a.toReal ∈ Ival.ofRat c.prec (b.toRat-a.toRat) := by
      simpa only [Dy.toReal_def, Rat.cast_sub] using
        Ival.mem_ofRat c.prec (b.toRat-a.toRat)
    have hxbox : ∀ x ∈ Set.Icc a.toReal b.toReal, x ∈ panelBox a b := by
      intro x hx
      simpa only [panelBox, Ival.mem_mk, Ival.loLe_some, Ival.leHi_some] using
        (show a.toReal ≤ x ∧ x ≤ b.toReal from hx)
    have hext : ∀ x ∈ Set.Ioo a.toReal b.toReal, ext.real x = e.real x := by
      intro x hx
      cases hs : specialize c (panelBox a b) e with
      | none => simp [ext, hs]
      | some f =>
        dsimp only [ext]
        rw [hs]
        change f.real x = e.real x
        apply specialize_sound hc hs (hxbox x ⟨hx.1.le, hx.2.le⟩)
        intro lo hi hlo hhi
        have ha : lo = a := Option.some.inj hlo.symm
        have hb : hi = b := Option.some.inj hhi.symm
        simpa [ha, hb] using hx
    have hv : ∀ x ∈ Set.Ioo a.toReal b.toReal, e.real x ∈ V := by
      intro x hx
      rw [← hext x hx]
      exact prepareEval_sound hc ext (hxbox x ⟨hx.1.le, hx.2.le⟩)
    have hne : ∃ v : ℝ, v ∈ V :=
      ⟨ext.real a.toReal, prepareEval_sound hc ext (hxbox _ ⟨le_rfl,hab⟩)⟩
    have hh := integral_mem_mul (p := c.prec) hab e.measurable hfinite hL hv hne
    exact Option.some.inj h ▸ hh
  · simp at h

theorem directPanel_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b : Dy}
    (hab : a.toReal ≤ b.toReal) {I : Ival}
    (h : directPanel c e a b = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  cases ho : oscillatoryPanel c e a b with
  | none =>
    exact directPanelCoarse_sound hc hab (by simpa [directPanel, ho] using h)
  | some J =>
    have hI : J = I := by simpa [directPanel, ho] using h
    exact hI ▸ oscillatoryPanel_sound ho

theorem NodeTable.positive {c : Ctx} {t : NodeTable}
    (h : t.check c = true) : 0 < t.roots.length := by
  cases hn : t.roots.length with
  | zero => simp [NodeTable.check, hn] at h
  | succ n => omega

theorem ellipseBox_mem {c : Ctx} {a b ρ : Dy} (hρ : 1 < ρ.toReal)
    {z : ℂ} (hz : z ∈ ellipse ρ.toReal) :
    affine a.toReal b.toReal z ∈ ellipseBox c a b ρ := by
  obtain ⟨hre, him⟩ := ellipse_in_rectangle hρ hz
  have hmid : (a.toReal+b.toReal)/2 ∈
      Ival.ofRat c.prec ((a.toRat+b.toRat)/2) := by
    simpa [Dy.toReal_def] using Ival.mem_ofRat c.prec ((a.toRat+b.toRat)/2)
  have hdelta : (b.toReal-a.toReal)/2 ∈
      Ival.ofRat c.prec ((b.toRat-a.toRat)/2) := by
    simpa [Dy.toReal_def] using Ival.mem_ofRat c.prec ((b.toRat-a.toRat)/2)
  have hrect : z ∈ (⟨Ival.ofRats c.prec (-((ρ.toRat+1/ρ.toRat)/2))
      ((ρ.toRat+1/ρ.toRat)/2), Ival.ofRats c.prec (-((ρ.toRat-1/ρ.toRat)/2))
      ((ρ.toRat-1/ρ.toRat)/2)⟩ : CBox) := by
    constructor
    · apply Ival.mem_ofRats
      · simpa [Dy.toReal_def, ellipseX, one_div] using (abs_le.mp hre).1
      · simpa [Dy.toReal_def, ellipseX, one_div] using (abs_le.mp hre).2
    · apply Ival.mem_ofRats
      · simpa [Dy.toReal_def, ellipseY, one_div] using (abs_le.mp him).1
      · simpa [Dy.toReal_def, ellipseY, one_div] using (abs_le.mp him).2
  exact CBox.mem_add (CBox.mem_ofReal hmid) (CBox.mem_mul (CBox.mem_ofReal hdelta) hrect)

theorem real_mem_affine_ellipse {a b x ρ : ℝ} (hab : a < b) (hρ : 1 < ρ)
    (hx : x ∈ Set.Icc a b) : (x : ℂ) ∈ affine a b '' ellipse ρ := by
  let t := (x-(a+b)/2)/((b-a)/2)
  have hd : 0 < (b-a)/2 := by linarith
  have ht : t ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hd).mpr
      linarith [hx.1]
    · apply (div_le_iff₀ hd).mpr
      linarith [hx.2]
  refine ⟨(t : ℂ), real_mem_ellipse hρ ht, ?_⟩
  have heq : (a+b)/2+(b-a)/2*t = x := by
    dsimp only [t]
    rw [mul_div_cancel₀ _ (ne_of_gt hd)]
    ring
  simpa only [affine, ← Complex.ofReal_mul, ← Complex.ofReal_add] using
    congrArg Complex.ofReal heq

/-- Geometric transport and branch selection for the complex bound. -/
theorem analyticBound_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b ρ M : Dy}
    (hab : a.toReal < b.toReal)
    (h : analyticBound c e a b ρ = some M) :
    1 < ρ.toReal ∧ 0 ≤ M.toReal ∧
      ∃ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F ((affine a.toReal b.toReal) '' ellipse ρ.toReal) ∧
        (∀ z ∈ ellipse ρ.toReal, ‖F (affine a.toReal b.toReal z)‖ ≤ M.toReal) ∧
        (∀ x ∈ Set.Ioo a.toReal b.toReal, F x = (e.real x : ℂ)) := by
  cases hext : specialize c (panelBox a b) e with
  | none => simp [analyticBound, hext] at h
  | some ext =>
    have hh : analyticBoundSpecialized c ext a b ρ = some M := by
      simpa [analyticBound, hext] using h
    unfold analyticBoundSpecialized at hh
    split at hh
    · simp at hh
    · rename_i hrho
      have hρ : 1 < ρ.toReal := by
        have ht : Dy.ltB Dy.one ρ = true := by simpa using hrho
        simpa [Dy.toReal_def] using Dy.toReal_lt_of_ltB ht
      dsimp only at hh
      split at hh
      · simp at hh
      · rename_i hreg
        have hr : regularCheck c ext (ellipseBox c a b ρ) = true := by simpa using hreg
        have hm : ∀ z ∈ ellipse ρ.toReal,
            ‖ext.complex (affine a.toReal b.toReal z)‖ ≤ M.toReal := by
          intro z hz
          exact analyticMagnitude_sound hc hr (ellipseBox_mem hρ hz) hh
        refine ⟨hρ, (norm_nonneg _).trans (hm 0 (real_mem_ellipse hρ (by norm_num))),
          ext.complex, (Term.analytic (regularCheck_sound hc ext hr)).mono ?_, hm, ?_⟩
        · rintro _ ⟨z, hz, rfl⟩
          exact ellipseBox_mem hρ hz
        · intro x hx
          have hxe := real_mem_affine_ellipse hab hρ ⟨hx.1.le,hx.2.le⟩
          have hxbox : (x : ℂ) ∈ ellipseBox c a b ρ := by
            obtain ⟨z, hz, heq⟩ := hxe
            exact heq ▸ ellipseBox_mem hρ hz
          rw [Term.agrees (regularCheck_sound hc ext hr) hxbox]
          congr 1
          apply specialize_sound hc hext
          · exact ⟨fun lo hlo => by cases Option.some.inj hlo; exact hx.1.le,
              fun hi hhi => by cases Option.some.inj hhi; exact hx.2.le⟩
          · intro lo hi hlo hhi
            cases Option.some.inj hlo
            cases Option.some.inj hhi
            exact hx

theorem gaussSamples_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b : Dy}
    {t : NodeTable} {x : Fin t.roots.length → ℝ}
    (ht : t.check c = true)
    (hx : ∀ i, x i ∈ rootIval (t.roots[i]) ∧
      gaussWeight t.roots.length (x i) ∈ (t.weights c).getD i.val Ival.top) :
    ((b.toReal - a.toReal) / 2) *
      gaussSum x (fun z => e.real ((a.toReal + b.toReal) / 2 +
        (b.toReal - a.toReal) / 2 * z)) ∈
      gaussSamples c e a b t (t.weights c) := by
  have hwlen : (t.weights c).length = t.roots.length := by
    have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp ht).1).2
    simpa only [NodeTable.weights, beq_iff_eq] using hh
  let mid := Ival.ofRat c.prec ((a.toRat+b.toRat)/2)
  let delta := Ival.ofRat c.prec ((b.toRat-a.toRat)/2)
  have hmid : (a.toReal+b.toReal)/2 ∈ mid := by
    simpa [mid, Dy.toReal_def] using Ival.mem_ofRat c.prec ((a.toRat+b.toRat)/2)
  have hdelta : (b.toReal-a.toReal)/2 ∈ delta := by
    simpa [delta, Dy.toReal_def] using Ival.mem_ofRat c.prec ((b.toRat-a.toRat)/2)
  let v : Fin t.roots.length → ℝ := fun i => gaussWeight t.roots.length (x i) *
    e.real ((a.toReal+b.toReal)/2+(b.toReal-a.toReal)/2*x i)
  let vals := (t.roots.zip (t.weights c)).map fun (r,w) =>
    mulSigned c.prec w (prepareEval c e (Ival.add c.prec mid (Ival.mul c.prec delta (rootIval r))))
  have hvals : List.Forall₂ (fun (x : ℝ) (I : Ival) => x ∈ I) (List.ofFn v) vals := by
    apply List.forall₂_of_length_eq_of_get
    · simp [vals, hwlen]
    · intro i hi hj
      have hir : i < t.roots.length := by simpa using hi
      have hiw : i < (t.weights c).length := by omega
      have hnode := hx ⟨i,hir⟩
      have hweight : gaussWeight t.roots.length (x ⟨i,hir⟩) ∈ (t.weights c)[i] := by
        simpa only [List.getD_eq_getElem _ _ hiw] using hnode.2
      have hp := Ival.mem_add (p := c.prec) hmid (Ival.mem_mul (p := c.prec) hdelta hnode.1)
      have hv := mem_mulSigned (p := c.prec) hweight (prepareEval_sound hc e hp)
      simpa [vals, v] using hv
  have hsum := balancedSum_mem (p := c.prec) hvals
  simpa only [List.sum_ofFn, v, Intgrl.gaussSum, gaussSamples, mid, delta, vals] using
    mem_mulSigned hdelta hsum

theorem errorBound_sound {c : Ctx} {n : ℕ} {a b ρ M err : Dy}
    (hn : 0 < n) (hab : a.toReal < b.toReal)
    (hρ : 1 < ρ.toReal) (hM : 0 ≤ M.toReal)
    (h : errorBound c n a b ρ M = some err) :
    glError n ρ.toReal (((b.toReal - a.toReal) / 2) * M.toReal) ≤ err.toReal := by
  -- Directed rounding is sound even without the analytic theorem's hypotheses.
  clear hn hab hρ hM
  cases hk : binaryRho ρ with
  | none =>
    have hhalf : (b.toReal-a.toReal)/2 ∈ Ival.ofRat c.prec ((b.toRat-a.toRat)/2) := by
      simpa [Dy.toReal_def] using Ival.mem_ofRat c.prec ((b.toRat-a.toRat)/2)
    have hv := Ival.mem_div (p := c.prec)
      (Ival.mem_mul (p := c.prec) (Ival.mem_ofRat c.prec 64)
        (Ival.mem_mul (p := c.prec) hhalf (Ival.mem_pt M)))
      (Ival.mem_mul (p := c.prec) (Ival.mem_ofRat c.prec 15)
        (Ival.mem_mul (p := c.prec) (Ival.mem_sub (p := c.prec) (Ival.mem_pt ρ) Ival.mem_one)
          (Ival.mem_npow (p := c.prec) (Ival.mem_pt ρ) (2*n-1))))
    have he := h
    simp only [errorBound, hk] at he
    have hh := hv.2 err he
    convert hh using 1
    simp only [glError, Rat.cast_ofNat]
    ring
  | some k =>
    obtain ⟨hkpos,hr⟩ := binaryRho_sound hk
    have herr : binaryError (binaryErrorBase c a b M k) k n = err := by
      simpa only [errorBound, hk, Option.some.injEq] using h
    have hpow : 1 ≤ 2^k := Nat.one_le_two_pow
    have hden : (Dy.ofNat (15*(2^k-1))).toRat ≠ 0 := by
      have hp : 1 < (2 : Nat)^k := Nat.one_lt_pow (by omega) (by omega)
      simp only [Dy.toRat_ofNat, ne_eq, Nat.cast_eq_zero]
      omega
    have hb := Dy.le_divU c.prec (Dy.scale2 ((b.add a.neg).mul M) 5)
      (Dy.ofNat (15*(2^k-1))) hden
    have hb' : (Dy.scale2 ((b.add a.neg).mul M) 5).toReal /
        (Dy.ofNat (15*(2^k-1))).toReal ≤ (binaryErrorBase c a b M k).toReal := by
      dsimp only [Dy.toReal_def, binaryErrorBase]
      exact_mod_cast hb
    have hbase : 32*(b.toReal-a.toReal)*M.toReal / (15*((2 : ℝ)^k-1)) ≤
        (binaryErrorBase c a b M k).toReal := by
      convert hb' using 1
      simp [Dy.toReal_def, Nat.cast_sub hpow]
      ring
    have hformula : glError n ρ.toReal (((b.toReal-a.toReal)/2)*M.toReal) =
        (32*(b.toReal-a.toReal)*M.toReal / (15*((2 : ℝ)^k-1))) *
          (2 : ℝ)^(-((k*(2*n-1) : Nat) : Int)) := by
      simp only [glError, hr, zpow_neg, zpow_natCast, ← pow_mul,
        div_eq_mul_inv, mul_inv_rev]
      ring
    rw [hformula, ← herr]
    have hh := mul_le_mul_of_nonneg_right hbase
      (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 2) (-((k*(2*n-1) : Nat) : Int))))
    simpa [binaryError, Dy.toReal_def] using hh

theorem gaussPanel_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b ρ : Dy}
    (hab : a.toReal < b.toReal) {t : NodeTable} (ht : t.check c = true)
    {I : Ival} (h : gaussPanel c e a b ρ t (t.weights c) = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  unfold gaussPanel at h
  cases hM : analyticBound c e a b ρ with
  | none => simp [hM] at h
  | some M =>
    rw [hM] at h
    cases herr : errorBound c t.roots.length a b ρ M with
    | none => simp [herr] at h
    | some err =>
      change (errorBound c t.roots.length a b ρ M).bind
        (fun err => some (Ival.widen c.prec (gaussSamples c e a b t (t.weights c)) err)) =
          some I at h
      rw [herr] at h
      have heq : Ival.widen c.prec (gaussSamples c e a b t (t.weights c)) err = I :=
        Option.some.inj h
      subst I
      obtain ⟨hρ, hM0, F, hF, hbound, hagree⟩ := analyticBound_sound hc hab hM
      obtain ⟨x, hx, hmem⟩ := t.sound hc ht
      have hn := NodeTable.positive ht
      have hgl := gauss_error_real_affine hn hx hab hρ hM0 hF hbound hagree
      exact ⟨hgl.1, Ival.mem_widen (gaussSamples_sound hc ht hmem)
        (hgl.2.trans (errorBound_sound hn hab hρ hM0 herr))⟩

end Lynth.Interval.Integral
