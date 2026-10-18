import Lynth.Interval.Integral.NestedShiftProof
import Lynth.Interval.Integral.NestedMeasurable
import Lynth.Interval.Integral.Math.NestedAnalysis

/-! Soundness of the elementary integral formula recognizers. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl MeasureTheory

theorem powerKernel_semantics {n : Nat} {base f : Expr} {q : ℚ}
    (h : powerKernel n base f = some q) (xs : List ℝ)
    (hb : base.Converges xs) (hp : 0 < base.real xs) :
    f.Converges xs ∧ f.real xs = (base.real xs)^(q : ℝ) := by
  unfold powerKernel at h
  fun_cases powerKernel n base f <;>
    (try simp_all only [reduceCtorEq,beq_iff_eq,Bool.and_eq_true])
  all_goals
    try simp_all only [NExpr.Converges,NExpr.real,Unary.real,Binary.real,
      Rat.cast_one,Real.sqrt_eq_rpow,one_div]

  all_goals
    split at h <;> simp_all
  all_goals
    subst q
    norm_num [Real.rpow_natCast,Real.rpow_neg hp.le,Real.rpow_neg_one]


theorem finite_domain_of_interval {k : NDomain} (hk : k.finite = true)
    {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hi : IntervalIntegrable F volume a b) :
    k.Converges F a b ∧ k.value F a b = ∫ x in a..b, F x := by
  cases k with
  | interval => exact ⟨hi,rfl⟩
  | icc =>
    exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi,by
      simp only [NDomain.value,intervalIntegral.integral_of_le hab,
        integral_Icc_eq_integral_Ioc]⟩
  | ioc =>
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi,by
      simp only [NDomain.value,intervalIntegral.integral_of_le hab]⟩
  | ico =>
    exact ⟨(intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp hi,by
      simp only [NDomain.value,intervalIntegral.integral_of_le hab,
        integral_Ico_eq_integral_Ioc]⟩
  | ioo =>
    exact ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi,by
      simp only [NDomain.value,intervalIntegral.integral_of_le hab,
        integral_Ioc_eq_integral_Ioo]⟩
  | right | left | whole => simp [NDomain.finite] at hk

theorem finite_integral_semantics {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} (ha : a.Converges xs) (hb : b.Converges xs)
    (hab : a.real xs ≤ b.real xs) {G : ℝ → ℝ}
    (hG : IntervalIntegrable G volume (a.real xs) (b.real xs))
    (hpoint : ∀ x ∈ Set.Ioo (a.real xs) (b.real xs),
      f.Converges (xs++[x]) ∧ f.real (xs++[x]) = G x) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = ∫ x in a.real xs..b.real xs, G x := by
  have he : (Set.uIoo (a.real xs) (b.real xs)).EqOn (fun x => f.real (xs++[x])) G := by
    intro x hx
    exact (hpoint x (by simpa only [Set.uIoo_of_le hab] using hx)).2
  have hi := (intervalIntegrable_congr_uIoo he).mpr hG
  have hd := finite_domain_of_interval hk hab hi
  refine ⟨⟨ha,hb,hd.1,?_⟩,hd.2.trans (intervalIntegral.integral_congr_uIoo he)⟩
  cases k <;> simp only [NDomain.finite,Bool.false_eq_true] at hk
  all_goals simpa only [Set.uIoo_of_le hab] using fun x hx => (hpoint x hx).1

theorem finite_power_right {a b p : ℝ} (hab : a ≤ b) (hp : -1 < p) :
    IntervalIntegrable (fun x : ℝ => (b-x)^p) volume a b ∧
      (∫ x in a..b, (b-x)^p) = (b-a)^(p+1)/(p+1) := by
  have h := finite_power_value (a := 0) (b := b-a) (by linarith) hp
  simp only [sub_zero] at h
  constructor
  · simpa only [sub_zero,sub_sub_cancel] using (h.1.comp_sub_left b).symm
  · rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x^p)]
    simpa only [sub_self,sub_zero] using h.2

theorem power_formula_left {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} (hsa : a.scoped xs.length = true)
    (ha : a.Converges xs) (hb : b.Converges xs) {q : ℚ}
    (hq : -1 < q) (hab : a.real xs ≤ b.real xs)
    (h : powerKernel xs.length
      (sub (.var xs.length) (if a.hasIntegral then a.shift xs.length 1 else a)) f = some q) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = (b.real xs-a.real xs)^((q:ℝ)+1)/((q:ℝ)+1) := by
  have hq' : (-1:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hG := finite_power_value hab hq'
  have hh := finite_integral_semantics (f := f) hk ha hb hab hG.1
  apply (fun H => ⟨H.1,H.2.trans hG.2⟩) (hh ?_)
  intro x hx
  have hend := endpoint_body_semantics hsa x
  have hbase : (sub (.var xs.length)
      (if a.hasIntegral then a.shift xs.length 1 else a)).real (xs++[x]) = x-a.real xs := by
    simp [sub_real,NExpr.real,hend.1]
  have hconv : (sub (.var xs.length)
      (if a.hasIntegral then a.shift xs.length 1 else a)).Converges (xs++[x]) :=
    (sub_converges _ _ _).mpr ⟨trivial,hend.2.mpr ha⟩
  simpa only [hbase] using powerKernel_semantics h (xs++[x]) hconv
    (by rw [hbase]; exact sub_pos.mpr hx.1)

theorem power_formula_right {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} (hsb : b.scoped xs.length = true)
    (ha : a.Converges xs) (hb : b.Converges xs) {q : ℚ}
    (hq : -1 < q) (hab : a.real xs ≤ b.real xs)
    (h : powerKernel xs.length
      (sub (if b.hasIntegral then b.shift xs.length 1 else b) (.var xs.length)) f = some q) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = (b.real xs-a.real xs)^((q:ℝ)+1)/((q:ℝ)+1) := by
  have hq' : (-1:ℝ) < (q:ℝ) := by exact_mod_cast hq
  have hG := finite_power_right hab hq'
  have hh := finite_integral_semantics (f := f) hk ha hb hab hG.1
  apply (fun H => ⟨H.1,H.2.trans hG.2⟩) (hh ?_)
  intro x hx
  have hend := endpoint_body_semantics hsb x
  have hbase : (sub (if b.hasIntegral then b.shift xs.length 1 else b)
      (.var xs.length)).real (xs++[x]) = b.real xs-x := by
    simp [sub_real,NExpr.real,hend.1]
  have hconv : (sub (if b.hasIntegral then b.shift xs.length 1 else b)
      (.var xs.length)).Converges (xs++[x]) :=
    (sub_converges _ _ _).mpr ⟨hend.2.mpr hb,trivial⟩
  simpa only [hbase] using powerKernel_semantics h (xs++[x]) hconv
    (by rw [hbase]; exact sub_pos.mpr hx.2)

theorem log_formula {k : NDomain} (hk : k.finite = true)
    {b : Expr} {xs : List ℝ} (hb : b.Converges xs) (hpos : 0 ≤ b.real xs) :
    (NExpr.integral k (.rat 0) b (.unary .log (.var xs.length))).Converges xs ∧
      (NExpr.integral k (.rat 0) b (.unary .log (.var xs.length))).real xs =
        b.real xs*(Real.log (b.real xs)-1) := by
  have hG := finite_log_value hpos
  have hh := finite_integral_semantics (f := .unary .log (.var xs.length)) hk
    (a := .rat 0) (by trivial) hb (by simpa only [NExpr.real,Rat.cast_zero] using hpos)
    (by simpa only [NExpr.real,Rat.cast_zero] using hG.1)
    (fun x _ => ⟨trivial,by simp [NExpr.real,Unary.real]⟩)
  exact ⟨hh.1,hh.2.trans (by simpa only [NExpr.real,Rat.cast_zero] using hG.2)⟩

theorem neg_log_formula {k : NDomain} (hk : k.finite = true)
    {b : Expr} {xs : List ℝ} (hb : b.Converges xs) (hpos : 0 ≤ b.real xs) :
    (NExpr.integral k (.rat 0) b (neg (.unary .log (.var xs.length)))).Converges xs ∧
      (NExpr.integral k (.rat 0) b (neg (.unary .log (.var xs.length)))).real xs =
        b.real xs*(1-Real.log (b.real xs)) := by
  have hG := finite_log_value hpos
  have hh := finite_integral_semantics (f := neg (.unary .log (.var xs.length))) hk
    (a := .rat 0) (by trivial) hb (by simpa only [NExpr.real,Rat.cast_zero] using hpos)
    (by
      simp only [NExpr.real,Rat.cast_zero]
      exact hG.1.neg)
    (G := fun x => -Real.log x) (fun x _ => ⟨by trivial,by simp [neg_real,NExpr.real,Unary.real]⟩)
  refine ⟨hh.1,hh.2.trans ?_⟩
  rw [intervalIntegral.integral_neg]
  simp only [NExpr.real,Rat.cast_zero]
  rw [hG.2]
  ring

theorem pure_append_unused {e : Expr} (hp : e.hasIntegral = false) {xs : List ℝ}
    (hu : e.uses xs.length = false) (x : ℝ) : e.real (xs++[x]) = e.real xs := by
  apply pure_env_congr hp
  intro i hi
  have hne : i ≠ xs.length := by intro he; subst i; rw [hu] at hi; contradiction
  by_cases hib : i < xs.length
  · simp [List.getElem?_append,hib]
  · simp [List.getElem?_append,hib,show i-xs.length ≠ 0 by omega]

theorem integral_semantics_of_eq {k : NDomain} {a b f : Expr} {xs : List ℝ}
    (ha : a.Converges xs) (hb : b.Converges xs) {G : ℝ → ℝ}
    (hG : k.Converges G (a.real xs) (b.real xs))
    (hpoint : ∀ x, f.Converges (xs++[x]) ∧ f.real (xs++[x]) = G x) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = k.value G (a.real xs) (b.real xs) := by
  have he : (fun x => f.real (xs++[x])) = G := funext (fun x => (hpoint x).2)
  exact ⟨⟨ha,hb,he ▸ hG,fun x _ => (hpoint x).1⟩,by simp only [NExpr.real,he]⟩

theorem exp_formula_right {a b c : Expr} {xs : List ℝ}
    (ha : a.Converges xs) (hb : b.Converges xs)
    (hp : c.hasIntegral = false) (hu : c.uses xs.length = false) :
    (NExpr.integral .right a b (.unary .exp (.binary .sub c (.var xs.length)))).Converges xs ∧
      (NExpr.integral .right a b (.unary .exp (.binary .sub c (.var xs.length)))).real xs =
        Real.exp (c.real xs-a.real xs) := by
  have hG := right_exp_value (a.real xs) (c.real xs)
  have hh := integral_semantics_of_eq (f := .unary .exp (.binary .sub c (.var xs.length)))
    (k := .right) ha hb hG.1 (G := fun x => Real.exp (c.real xs-x)) (fun x =>
      ⟨⟨converges_of_noIntegral hp _,trivial⟩,by
        simp [NExpr.real,Unary.real,Binary.real,pure_append_unused hp hu x]⟩)
  exact ⟨hh.1,hh.2.trans hG.2⟩

theorem exp_formula_left_add {a b c : Expr} {xs : List ℝ}
    (ha : a.Converges xs) (hb : b.Converges xs)
    (hp : c.hasIntegral = false) (hu : c.uses xs.length = false) :
    (NExpr.integral .left a b (.unary .exp (.binary .add c (.var xs.length)))).Converges xs ∧
      (NExpr.integral .left a b (.unary .exp (.binary .add c (.var xs.length)))).real xs =
        Real.exp (c.real xs+a.real xs) := by
  have hG := left_exp_value (a.real xs) (c.real xs)
  have hh := integral_semantics_of_eq (f := .unary .exp (.binary .add c (.var xs.length)))
    (k := .left) ha hb hG.1 (G := fun x => Real.exp (c.real xs+x)) (fun x =>
      ⟨⟨converges_of_noIntegral hp _,trivial⟩,by
        simp [NExpr.real,Unary.real,Binary.real,pure_append_unused hp hu x]⟩)
  exact ⟨hh.1,hh.2.trans hG.2⟩

theorem exp_formula_left_sub {a b c : Expr} {xs : List ℝ}
    (ha : a.Converges xs) (hb : b.Converges xs)
    (hp : c.hasIntegral = false) (hu : c.uses xs.length = false) :
    (NExpr.integral .left a b (.unary .exp (.binary .sub (.var xs.length) c))).Converges xs ∧
      (NExpr.integral .left a b (.unary .exp (.binary .sub (.var xs.length) c))).real xs =
        Real.exp (a.real xs-c.real xs) := by
  have hG := left_exp_value (a.real xs) (-c.real xs)
  have hh := integral_semantics_of_eq (f := .unary .exp (.binary .sub (.var xs.length) c))
    (k := .left) ha hb (by simpa only [NDomain.Converges,neg_add_eq_sub] using hG.1)
    (G := fun x => Real.exp (x-c.real xs)) (fun x =>
      ⟨⟨trivial,converges_of_noIntegral hp _⟩,by
        simp [NExpr.real,Unary.real,Binary.real,pure_append_unused hp hu x]⟩)
  refine ⟨hh.1,hh.2.trans ?_⟩
  simpa only [NDomain.value,neg_add_eq_sub] using hG.2

private theorem orElse_some {α : Type*} {A B : Option α} {q : α}
    (h : (A <|> B) = some q) : A = some q ∨ B = some q := by
  cases ha : A <;> simp_all

theorem formula_sound {kind : NDomain} {a b f : Expr} {form : Formula} {xs : List ℝ}
    (hsa : a.scoped xs.length = true) (hsb : b.scoped xs.length = true)
    (ha : a.Converges xs) (hb : b.Converges xs)
    (h : formula xs.length kind a b f = some form)
    (hg : ∀ g ∈ form.nonnegative, 0 ≤ g.real xs) :
    (NExpr.integral kind a b f).Converges xs ∧
      (NExpr.integral kind a b f).real xs = form.value.real xs := by
  unfold formula at h
  fun_cases formula xs.length kind a b f
  all_goals
    dsimp +zetaDelta only at *
    try simp_all only [bind,pure,Option.some.injEq,
      reduceCtorEq,↓reduceIte]
  all_goals
    try simp_all only [beq_iff_eq,Bool.and_eq_true,
      Bool.not_eq_false,Bool.not_eq_true_eq_eq_false]
  all_goals try subst form
  case case1 =>
    have hG := right_exp_value (a.real xs) 0
    have hh := integral_semantics_of_eq (f := .unary .exp (neg (.var xs.length)))
      (k := .right) ha hb hG.1 (G := fun x => Real.exp (0-x)) (fun x =>
        ⟨by trivial,by simp [neg_real,NExpr.real,Unary.real]⟩)
    exact ⟨hh.1,hh.2.trans (by
      simpa only [NDomain.value,NExpr.real,Unary.real,neg_real,zero_sub] using hG.2)⟩
  case case2 =>
    rename_i y c y' hk hguards hneq
    simpa only [NExpr.real,Unary.real,sub_real] using
      exp_formula_right (c := c) ha hb hguards.2 hguards.1.2
  case case5 =>
    have hG := left_exp_value (a.real xs) 0
    have hh := integral_semantics_of_eq (f := .unary .exp (.var xs.length))
      (k := .left) ha hb hG.1 (G := fun x => Real.exp (0+x)) (fun x =>
        ⟨by trivial,by simp [NExpr.real,Unary.real]⟩)
    exact ⟨hh.1,hh.2.trans (by
      simpa only [NDomain.value,NExpr.real,Unary.real,zero_add] using hG.2)⟩
  case case6 =>
    rename_i y c y' hnotright hk hguards hneq
    simpa only [NExpr.real,Unary.real,add_real] using
      exp_formula_left_add (c := c) ha hb hguards.2 hguards.1.2
  case case8 =>
    rename_i y y' c hnotright hk hguards hneq
    simpa only [NExpr.real,Unary.real,sub_real] using
      exp_formula_left_sub (c := c) ha hb hguards.2 hguards.1.2
  case case12 =>
    rename_i y hnotright hnotleft hk hbody
    have hpos : 0 ≤ b.real xs := hg b (by simp)
    simpa only [mul_real,sub_real,NExpr.real,Unary.real,Rat.cast_one] using log_formula hk hb hpos
  case case13 =>
    rename_i y hnotright hnotleft hk hnotlog hbody
    have hpos : 0 ≤ b.real xs := hg b (by simp)
    simpa only [mul_real,sub_real,NExpr.real,Unary.real,Rat.cast_one] using
      neg_log_formula hk hb hpos
  case case14 =>
    rename_i y width bodyA bodyB hnotright hnotleft hk hnotlog hnotneglog
    let K0 := if a == .rat 0 then powerKernel xs.length (.var xs.length) f else none
    let KL := powerKernel xs.length
      (sub (.var xs.length) (if a.hasIntegral then a.shift xs.length 1 else a)) f
    let KR := powerKernel xs.length
      (sub (if b.hasIntegral then b.shift xs.length 1 else b) (.var xs.length)) f
    change ((K0 <|> KL <|> KR).bind fun q => if q ≤ -1 then none else
      some ⟨div (rpow (sub b a) (q+1)) (.rat (q+1)),some (sub b a),none⟩) = some form at h
    cases hK : (K0 <|> KL <|> KR) with
    | none => simp only [hK,Option.bind_none,reduceCtorEq] at h
    | some q =>
      rw [hK] at h
      simp only [Option.bind_some] at h
      split at h
      · contradiction
      · rename_i hq
        have hq' : -1 < q := lt_of_not_ge hq
        have hform := Option.some.inj h
        subst form
        have hwidth := hg (sub b a) (by simp)
        have hab : a.real xs ≤ b.real xs := by rw [sub_real] at hwidth; linarith
        have hcases : K0 = some q ∨ KL = some q ∨ KR = some q := by
          rcases orElse_some hK with h | h
          · exact Or.inl h
          · exact Or.inr (orElse_some h)
        have hh : (NExpr.integral kind a b f).Converges xs ∧
            (NExpr.integral kind a b f).real xs =
              (b.real xs-a.real xs)^((q:ℝ)+1)/((q:ℝ)+1) := by
          rcases hcases with h0 | hl | hr
          · dsimp only [K0] at h0
            split at h0
            · rename_i haz
              have haz' : a = .rat 0 := by simpa using haz
              subst a
              apply power_formula_left hk hsa ha hb hq' hab
              have hz : sub (.var xs.length)
                  (if (NExpr.rat 0).hasIntegral then (NExpr.rat 0).shift xs.length 1 else .rat 0) =
                    .var xs.length := by rfl
              simpa only [hz] using h0
            · contradiction
          · exact power_formula_left hk hsa ha hb hq' hab hl
          · exact power_formula_right hk hsb ha hb hq' hab hr
        simpa only [div_real,rpow_real,sub_real,NExpr.real,Rat.cast_add,Rat.cast_one] using hh

end Lynth.Interval.Integral.Nested
