module

import all Lynth.Interval.Integral.Math.ComplexBranch
import all Lynth.Interval.Integral.Math.NestedSyntaxLemmas

/-! Real semantics of the complex-projection normalizers and branch
resolution used by the complex integral reduction. -/

namespace Intgrl
open Lynth.Interval.Integral.Nested MeasureTheory Set

theorem noInt_real_indep {e : NExpr} {n : Nat} (hi : e.hasIntegral = false)
    (hu : e.uses n = false) {env : List ℝ} (hn : env.length = n) (x : ℝ) :
    e.real (env ++ [x]) = e.real env := by
  induction e with
  | var i =>
    simp only [NExpr.uses, beq_eq_false_iff_ne] at hu
    simp only [NExpr.real]
    rcases lt_or_gt_of_ne hu with h | h
    · rw [List.getElem?_append_right (by omega), List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
    · rw [List.getElem?_append_left (by omega)]
  | rat | pi => rfl
  | unary op a ih => simp only [NExpr.real]; rw [ih hi hu]
  | pow a k ih => simp only [NExpr.real]; rw [ih hi hu]
  | rpow a q ih => simp only [NExpr.real]; rw [ih hi hu]
  | binary op a b iha ihb =>
    simp only [NExpr.hasIntegral, Bool.or_eq_false_iff] at hi
    simp only [NExpr.uses, Bool.or_eq_false_iff] at hu
    simp only [NExpr.real]; rw [iha hi.1 hu.1, ihb hi.2 hu.2]
  | integral => simp [NExpr.hasIntegral] at hi

theorem clean_sound (e : NExpr) (env : List ℝ) :
    (CParts.clean e).real env = e.real env ∧ ((CParts.clean e).Converges env ↔ e.Converges env) := by
  unfold CParts.clean
  split
  · exact ⟨rfl, Iff.rfl⟩
  · exact simplify_sound e env

theorem un_sound (op : Unary) (a : NExpr) (env : List ℝ) :
    (CParts.un op a).real env = op.real (a.real env) ∧
      ((CParts.un op a).Converges env → a.Converges env) := by
  unfold CParts.un
  split
  · cases op <;> simp [NExpr.real, Unary.real, NExpr.Converges, clean_sound]
  · cases op <;> simp [NExpr.real, Unary.real, NExpr.Converges, Rat.floor_cast, clean_sound]
  · simp only [clean_sound, NExpr.real, NExpr.Converges]
    exact ⟨trivial, id⟩

theorem rat_two_lit : ∀ h1 h2, (⟨Int.ofNat 2, 1, h1, h2⟩ : ℚ) = 2 := fun _ _ => rfl

theorem cleanUnary_sound (op : Unary) (a : NExpr) (env : List ℝ) :
    (complexCleanUnary op a).real env = op.real (a.real env) ∧
      ((complexCleanUnary op a).Converges env → a.Converges env) := by
  unfold complexCleanUnary
  split
  · rename_i hop
    have hop' : op = .sqrt := by simpa using hop
    subst hop'
    split
    · rename_i c
      simp only [NExpr.real, Unary.real, NExpr.Converges]
      exact ⟨(Real.sqrt_sq_eq_abs _).symm, id⟩
    · rename_i c d
      split
      · rename_i hcd
        have hcd' : c = d := by simpa using hcd
        subst hcd'
        obtain ⟨h1, h2⟩ := un_sound .sqrt c env
        refine ⟨?_, fun h => ⟨⟨h2 h, h2 h⟩, trivial⟩⟩
        rw [h1]
        simp only [NExpr.real, Unary.real, Binary.real, rat_two_lit, Rat.cast_ofNat]
        rcases le_or_gt 0 (c.real env) with hc | hc
        · rw [abs_of_nonneg hc]; congr 1; ring
        · rw [abs_of_neg hc, Real.sqrt_eq_zero'.2 hc.le]
          simp
      · exact un_sound _ _ env
    · rename_i c d
      split
      · rename_i hcd
        have hcd' : c = d := by simpa using hcd
        subst hcd'
        obtain ⟨h1, h2⟩ := un_sound .sqrt (neg c) env
        refine ⟨?_, fun h => ⟨⟨(neg_converges c env).1 (h2 h), (neg_converges c env).1 (h2 h)⟩,
          trivial⟩⟩
        rw [h1, neg_real]
        simp only [NExpr.real, Unary.real, Binary.real, rat_two_lit, Rat.cast_ofNat]
        rcases le_or_gt 0 (c.real env) with hc | hc
        · rw [abs_of_nonneg hc, Real.sqrt_eq_zero'.2 (by linarith)]
          simp
        · rw [abs_of_neg hc]; congr 1; ring
      · exact un_sound _ _ env
    · rename_i q
      split
      · rename_i hq
        simp only [NExpr.real, Unary.real, NExpr.Converges]
        refine ⟨(Real.sqrt_eq_zero'.2 (by exact_mod_cast hq : (q:ℝ) ≤ 0)).symm ▸ by simp, fun _ => trivial⟩
      · exact un_sound _ _ env
    · exact un_sound _ _ env
  · exact un_sound _ _ env

theorem cleanBinary_sound (op : Binary) (a b : NExpr) (env : List ℝ) :
    (complexCleanBinary op a b).real env = op.real (a.real env) (b.real env) ∧
      ((complexCleanBinary op a b).Converges env → a.Converges env ∧ b.Converges env) := by
  unfold complexCleanBinary
  split
  · rename_i a' b'
    refine ⟨by rw [sub_real]; simp [NExpr.real, Unary.real, Binary.real, sub_eq_add_neg],
      fun h => ?_⟩
    rw [sub_converges] at h; exact h
  · rename_i a' b'
    refine ⟨by rw [sub_real]; simp [NExpr.real, Unary.real, Binary.real]; ring, fun h => ?_⟩
    rw [sub_converges] at h; exact ⟨h.2, h.1⟩
  · rename_i a' b'
    refine ⟨by rw [add_real]; simp [NExpr.real, Unary.real, Binary.real, sub_eq_add_neg],
      fun h => ?_⟩
    rw [add_converges] at h; exact h
  · rename_i a' b' c'
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨rfl, hi⟩ := hc
      refine ⟨by simp [NExpr.real, Binary.real], fun h => ?_⟩
      exact ⟨noIntegral_converges hi env, h, noIntegral_converges hi env⟩
    · exact ⟨(simplify_sound _ env).1, fun h => (simplify_sound _ env).2.1 h⟩
  · rename_i a' b' c'
    split
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
      obtain ⟨rfl, hi⟩ := hc
      refine ⟨by simp [NExpr.real, Binary.real], fun h => ?_⟩
      exact ⟨⟨h, noIntegral_converges hi env⟩, noIntegral_converges hi env⟩
    · exact ⟨(simplify_sound _ env).1, fun h => (simplify_sound _ env).2.1 h⟩
  · rename_i a'
    split
    · rename_i hi
      simp only [Bool.not_eq_true'] at hi
      exact ⟨by simp [NExpr.real, Binary.real], fun _ => ⟨noIntegral_converges hi env, trivial⟩⟩
    · exact ⟨rfl, id⟩
  · rename_i b'
    split
    · rename_i hi
      simp only [Bool.not_eq_true'] at hi
      exact ⟨by simp [NExpr.real, Binary.real], fun _ => ⟨trivial, noIntegral_converges hi env⟩⟩
    · exact ⟨rfl, id⟩
  · exact ⟨(simplify_sound _ env).1, fun h => (simplify_sound _ env).2.1 h⟩

theorem cleanPow_sound (a : NExpr) (m : Nat) (env : List ℝ) :
    (complexCleanPow a m).real env = a.real env ^ m ∧
      ((complexCleanPow a m).Converges env → a.Converges env) := by
  unfold complexCleanPow
  split
  · simp [NExpr.real, NExpr.Converges]
  · exact ⟨pow_real _ _ _, (pow_converges _ _ _).1⟩

/-! Integral-freeness is preserved by the arithmetic normalizers. -/

theorem add_noInt {a b : NExpr} (ha : a.hasIntegral = false) (hb : b.hasIntegral = false) :
    (add a b).hasIntegral = false := by
  unfold add; split <;> simp_all [NExpr.hasIntegral]

theorem neg_noInt {a : NExpr} (ha : a.hasIntegral = false) : (neg a).hasIntegral = false := by
  unfold neg; split <;> simp_all [NExpr.hasIntegral]

theorem sub_noInt {a b : NExpr} (ha : a.hasIntegral = false) (hb : b.hasIntegral = false) :
    (sub a b).hasIntegral = false := by
  unfold sub
  split
  · rfl
  · split <;> (try split) <;> (try split) <;> simp_all [NExpr.hasIntegral, neg_noInt]

theorem mul_noInt {a b : NExpr} (ha : a.hasIntegral = false) (hb : b.hasIntegral = false) :
    (mul a b).hasIntegral = false := by
  unfold mul; split <;> (try split) <;> simp_all [NExpr.hasIntegral]

theorem div_noInt {a b : NExpr} (ha : a.hasIntegral = false) (hb : b.hasIntegral = false) :
    (div a b).hasIntegral = false := by
  unfold div; split <;> simp_all [NExpr.hasIntegral]

theorem pow_noInt {a : NExpr} (n : Nat) (ha : a.hasIntegral = false) :
    (pow a n).hasIntegral = false := by
  unfold pow
  split
  · rfl
  · split
    · exact ha
    · split
      · split <;> simp_all [NExpr.hasIntegral, neg_noInt]
      · simp_all [NExpr.hasIntegral]

theorem rpow_noInt {a : NExpr} (q : ℚ) (ha : a.hasIntegral = false) :
    (rpow a q).hasIntegral = false := by
  unfold rpow
  split
  · rfl
  · split
    · exact ha
    · split
      · exact pow_noInt _ ha
      · simp_all [NExpr.hasIntegral]

theorem simplify_noInt {e : NExpr} (h : e.hasIntegral = false) :
    (simplify e).hasIntegral = false := by
  induction e with
  | var | rat | pi => simpa [simplify] using h
  | unary op a ih =>
    cases op <;> simp_all [simplify, NExpr.hasIntegral, neg_noInt]
  | binary op a b iha ihb =>
    simp only [NExpr.hasIntegral, Bool.or_eq_false_iff] at h
    cases op <;> simp_all [simplify, NExpr.hasIntegral, add_noInt, sub_noInt, mul_noInt, div_noInt]
  | pow a n ih => simp_all [simplify, NExpr.hasIntegral, pow_noInt]
  | rpow a q ih => simp_all [simplify, NExpr.hasIntegral, rpow_noInt]
  | integral => simp [NExpr.hasIntegral] at h

theorem clean_noInt {e : NExpr} (h : e.hasIntegral = false) :
    (CParts.clean e).hasIntegral = false := by
  unfold CParts.clean; split
  · exact h
  · exact simplify_noInt h

theorem un_noInt (op : Unary) {a : NExpr} (h : a.hasIntegral = false) :
    (CParts.un op a).hasIntegral = false := by
  unfold CParts.un
  split
  · cases op <;> rfl
  · cases op <;> rfl
  · exact clean_noInt (by simpa [NExpr.hasIntegral] using h)

theorem negative_noInt {a : NExpr} (h : a.hasIntegral = false) :
    (CParts.negative a).hasIntegral = false := by
  show (CParts.un .floor (CParts.div a (CParts.un .sqrt (CParts.add (.rat 1)
    (CParts.sq a))))).hasIntegral = false
  refine un_noInt _ (clean_noInt ?_)
  simp only [NExpr.hasIntegral, h, Bool.false_or]
  refine un_noInt _ (clean_noInt ?_)
  simp only [NExpr.hasIntegral, Bool.false_or, CParts.sq]
  exact clean_noInt (by simpa [NExpr.hasIntegral] using h)

theorem negative_real (a : NExpr) (env : List ℝ) :
    (CParts.negative a).real env = if a.real env < 0 then -1 else 0 := by
  show (CParts.un .floor (CParts.div a (CParts.un .sqrt (CParts.add (.rat 1)
    (CParts.sq a))))).real env = _
  rw [(un_sound _ _ _).1, CParts.div, (clean_sound _ _).1]
  simp only [NExpr.real, Binary.real, Unary.real]
  rw [(un_sound _ _ _).1, CParts.add, (clean_sound _ _).1]
  simp only [NExpr.real, Binary.real, Unary.real, CParts.sq, (clean_sound _ _).1, Rat.cast_one]
  set x := a.real env
  have hs : |x| < Real.sqrt (1 + x ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by linarith)
  have hpos : 0 < Real.sqrt (1 + x ^ 2) := lt_of_le_of_lt (abs_nonneg _) hs
  split_ifs with h
  · have : ⌊x / Real.sqrt (1 + x ^ 2)⌋ = -1 := by
      rw [Int.floor_eq_iff]
      constructor
      · rw [le_div_iff₀ hpos]; rw [abs_of_neg h] at hs; push_cast; linarith
      · push_cast; rw [div_lt_iff₀ hpos]; linarith
    simp [this]
  · have : ⌊x / Real.sqrt (1 + x ^ 2)⌋ = 0 := by
      push Not at h
      rw [Int.floor_eq_iff]
      constructor
      · push_cast; exact div_nonneg h hpos.le
      · push_cast; rw [div_lt_iff₀ hpos]; rw [abs_of_nonneg h] at hs; linarith
    simp [this]

theorem isZero_real (a : NExpr) (env : List ℝ) :
    (CParts.isZero a).real env = if a.real env = 0 then 1 else 0 := by
  show (CParts.add (.rat 1) (CParts.add (CParts.negative a)
    (CParts.negative (CParts.neg a)))).real env = _
  simp only [CParts.add, CParts.neg, (clean_sound _ _).1, NExpr.real, Binary.real,
    Unary.real, negative_real, Rat.cast_one]
  rcases lt_trichotomy (a.real env) 0 with h | h | h
  · simp [h, h.ne, not_lt.2 (neg_nonneg.2 h.le)]
  · simp [h]
  · simp [h, h.ne', not_lt.2 h.le]

theorem ite_branch_sound' {b : Bool} {e N R M : NExpr} {env : List ℝ}
    (hb : b = true → e = N)
    (s : R.real env = N.real env) (c : N.Converges env)
    (hM : M.real env = e.real env ∧ (M.Converges env → e.Converges env)) :
    (if b then R else M).real env = e.real env ∧
      ((if b then R else M).Converges env → e.Converges env) := by
  split
  · rename_i h; obtain rfl := hb h; exact ⟨s, fun _ => c⟩
  · exact hM

set_option maxHeartbeats 1000000 in
theorem resolveAxisStep_sound {n : Nat} {positive : Bool} {env : List ℝ} {x : ℝ}
    (hx : env[n]? = some x) (hpos : if positive then 0 < x else x < 0) (e : NExpr) :
    (resolveAxisStep n positive e).real env = e.real env ∧
      ((resolveAxisStep n positive e).Converges env → e.Converges env) := by
  have hv : (NExpr.var n).real env = x := by simp [NExpr.real, hx]
  have spec1 : (NExpr.rat (if positive then 0 else -1)).real env =
      (CParts.negative (.var n)).real env := by
    rw [negative_real, hv]
    cases positive <;> simp at hpos <;> simp [NExpr.real, hpos, not_lt.2 hpos.le]
  have spec2 : (NExpr.rat (if positive then -1 else 0)).real env =
      (CParts.negative (neg (.var n))).real env := by
    rw [negative_real, neg_real, hv]
    cases positive <;> simp at hpos <;> simp [NExpr.real, hpos, not_lt.2 hpos.le]
  have c1 : (CParts.negative (.var n)).Converges env :=
    noIntegral_converges (negative_noInt rfl) env
  have c2 : (CParts.negative (neg (.var n))).Converges env :=
    noIntegral_converges (negative_noInt (neg_noInt rfl)) env
  induction e with
  | var | rat | pi | integral =>
    unfold resolveAxisStep
    split
    · rename_i h; rw [beq_iff_eq] at h; rw [h]; exact ⟨spec1, fun _ => c1⟩
    split
    · rename_i h; rw [beq_iff_eq] at h; rw [h]; exact ⟨spec2, fun _ => c2⟩
    exact ⟨rfl, id⟩
  | unary op a ih =>
    rw [resolveAxisStep]
    refine ite_branch_sound' beq_iff_eq.1 spec1 c1 (ite_branch_sound' beq_iff_eq.1 spec2 c2 ?_)
    obtain ⟨h3, h4⟩ := cleanUnary_sound op (resolveAxisStep n positive a) env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, ih.1], fun h => ih.2 (h4 h)⟩
  | binary op a b iha ihb =>
    rw [resolveAxisStep]
    refine ite_branch_sound' beq_iff_eq.1 spec1 c1 (ite_branch_sound' beq_iff_eq.1 spec2 c2 ?_)
    obtain ⟨h3, h4⟩ := cleanBinary_sound op (resolveAxisStep n positive a)
      (resolveAxisStep n positive b) env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, iha.1, ihb.1], fun h => ⟨iha.2 (h4 h).1, ihb.2 (h4 h).2⟩⟩
  | pow a m ih =>
    rw [resolveAxisStep]
    refine ite_branch_sound' beq_iff_eq.1 spec1 c1 (ite_branch_sound' beq_iff_eq.1 spec2 c2 ?_)
    obtain ⟨h3, h4⟩ := cleanPow_sound (resolveAxisStep n positive a) m env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, ih.1], fun h => ih.2 (h4 h)⟩
  | rpow a q ih =>
    rw [resolveAxisStep]
    refine ite_branch_sound' beq_iff_eq.1 spec1 c1 (ite_branch_sound' beq_iff_eq.1 spec2 c2 ?_)
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [rpow_real, ih.1], fun h => ih.2 ((rpow_converges _ _ _).1 h)⟩

set_option maxHeartbeats 1000000 in
theorem resolveUnitLog_sound {n : Nat} {env : List ℝ} {x : ℝ}
    (hx : env[n]? = some x) (h0 : 0 < x) (h1 : x < 1) (e : NExpr) :
    (resolveUnitLog n e).real env = e.real env ∧
      ((resolveUnitLog n e).Converges env → e.Converges env) := by
  have hv : (NExpr.unary .log (NExpr.var n)).real env = Real.log x := by
    simp [NExpr.real, Unary.real, hx]
  have hl : Real.log x < 0 := Real.log_neg h0 h1
  have s1 : (NExpr.rat 0).real env = (NExpr.unary .sqrt (.unary .log (.var n))).real env := by
    simp only [NExpr.real] at hv ⊢; rw [hv]; simp [Unary.real, Real.sqrt_eq_zero'.2 hl.le]
  have s2 : (neg (.unary .log (.var n))).real env =
      (NExpr.unary .abs (.unary .log (.var n))).real env := by
    rw [neg_real]; simp only [NExpr.real] at hv ⊢; rw [hv]; simp [Unary.real, abs_of_neg hl]
  have s3 : (NExpr.rat (-1)).real env = (CParts.negative (.unary .log (.var n))).real env := by
    rw [negative_real, hv]; simp [NExpr.real, hl]
  have s4 : (NExpr.rat 0).real env =
      (CParts.negative (neg (.unary .log (.var n)))).real env := by
    rw [negative_real, neg_real, hv]; simp [NExpr.real, hl.le]
  have c1 : (NExpr.unary .sqrt (.unary .log (.var n))).Converges env := trivial
  have c2 : (NExpr.unary .abs (.unary .log (.var n))).Converges env := trivial
  have c3 : (CParts.negative (.unary .log (.var n))).Converges env :=
    noIntegral_converges (negative_noInt rfl) env
  have c4 : (CParts.negative (neg (.unary .log (.var n)))).Converges env :=
    noIntegral_converges (negative_noInt (neg_noInt rfl)) env
  induction e with
  | var | rat | pi | integral =>
    unfold resolveUnitLog
    refine ite_branch_sound' beq_iff_eq.1 s1 c1 (ite_branch_sound' beq_iff_eq.1 s2 c2 (ite_branch_sound' beq_iff_eq.1 s3 c3
      (ite_branch_sound' beq_iff_eq.1 s4 c4 ?_)))
    exact ⟨rfl, id⟩
  | unary op a ih =>
    rw [resolveUnitLog]
    refine ite_branch_sound' beq_iff_eq.1 s1 c1 (ite_branch_sound' beq_iff_eq.1 s2 c2 (ite_branch_sound' beq_iff_eq.1 s3 c3
      (ite_branch_sound' beq_iff_eq.1 s4 c4 ?_)))
    obtain ⟨h3, h4⟩ := cleanUnary_sound op (resolveUnitLog n a) env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, ih.1], fun h => ih.2 (h4 h)⟩
  | binary op a b iha ihb =>
    rw [resolveUnitLog]
    refine ite_branch_sound' beq_iff_eq.1 s1 c1 (ite_branch_sound' beq_iff_eq.1 s2 c2 (ite_branch_sound' beq_iff_eq.1 s3 c3
      (ite_branch_sound' beq_iff_eq.1 s4 c4 ?_)))
    obtain ⟨h3, h4⟩ := cleanBinary_sound op (resolveUnitLog n a) (resolveUnitLog n b) env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, iha.1, ihb.1], fun h => ⟨iha.2 (h4 h).1, ihb.2 (h4 h).2⟩⟩
  | pow a m ih =>
    rw [resolveUnitLog]
    refine ite_branch_sound' beq_iff_eq.1 s1 c1 (ite_branch_sound' beq_iff_eq.1 s2 c2 (ite_branch_sound' beq_iff_eq.1 s3 c3
      (ite_branch_sound' beq_iff_eq.1 s4 c4 ?_)))
    obtain ⟨h3, h4⟩ := cleanPow_sound (resolveUnitLog n a) m env
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [h3, ih.1], fun h => ih.2 (h4 h)⟩
  | rpow a q ih =>
    rw [resolveUnitLog]
    refine ite_branch_sound' beq_iff_eq.1 s1 c1 (ite_branch_sound' beq_iff_eq.1 s2 c2 (ite_branch_sound' beq_iff_eq.1 s3 c3
      (ite_branch_sound' beq_iff_eq.1 s4 c4 ?_)))
    simp only [NExpr.real, NExpr.Converges]
    exact ⟨by rw [rpow_real, ih.1], fun h => ih.2 ((rpow_converges _ _ _).1 h)⟩


theorem interval_from_congr {α β : ℝ} (hab : α ≤ β) {G0 F : NExpr} {a b : NExpr} {env : List ℝ}
    (ha : a.real env = α) (hb : b.real env = β)
    (heq : ∀ x ∈ Ioo α β, G0.real (env ++ [x]) = F.real (env ++ [x]))
    (hc : (NExpr.integral .interval a b G0).Converges env) :
    IntervalIntegrable (fun x => F.real (env ++ [x])) volume α β ∧
      (NExpr.integral .interval a b G0).real env = ∫ x in α..β, F.real (env ++ [x]) := by
  obtain ⟨-, -, hi, -⟩ := hc
  simp only [NDomain.Converges, ha, hb] at hi
  have heq' : EqOn (fun x => G0.real (env ++ [x])) (fun x => F.real (env ++ [x])) (uIoo α β) := by
    rw [uIoo_of_le hab]; exact heq
  refine ⟨(intervalIntegrable_congr_uIoo heq').1 hi, ?_⟩
  simp only [NExpr.real, NDomain.value, ha, hb]
  exact intervalIntegral.integral_congr_uIoo heq'

theorem complexBranchIntegral_sound {n : Nat} {A B F G : NExpr} {env : List ℝ}
    (hn : env.length = n) (h : complexBranchIntegral n A B F = some G) (hG : G.Converges env) :
    (NExpr.integral .interval A B F).Converges env ∧
      (NExpr.integral .interval A B F).real env = G.real env := by
  unfold complexBranchIntegral at h
  split at h
  · simp at h
  rename_i hF
  simp only [Bool.not_eq_true] at hF
  split at h
  rotate_left
  · simp at h
  rename_i p
  split at h
  rotate_left
  · simp at h
  rename_i q
  split at h
  · simp at h
  rename_i hpq
  have hpq' : (p : ℝ) < q := by exact_mod_cast (not_le.1 hpq)
  simp only [Option.pure_def, Option.bind_eq_bind] at h
  have hx : ∀ x : ℝ, (env ++ [x])[n]? = some x := fun x => by simp [← hn]
  -- the unit-interval logarithm resolution
  set F' := (if (decide (0 ≤ p) && decide (q ≤ 1)) = true then resolveUnitLog n F else F)
    with hF'def
  have unitFix : ∀ E : NExpr, ∀ x ∈ Ioo (p : ℝ) q,
      (if (decide (0 ≤ p) && decide (q ≤ 1)) = true then resolveUnitLog n E else E).real
        (env ++ [x]) = E.real (env ++ [x]) := by
    intro E x hxI
    split
    · rename_i hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have h0 : (0 : ℝ) ≤ p := by exact_mod_cast hc.1
      have h1 : (q : ℝ) ≤ 1 := by exact_mod_cast hc.2
      exact (resolveUnitLog_sound (hx x) (by linarith [hxI.1]) (by linarith [hxI.2]) E).1
    · rfl
  have hF'eq : ∀ x ∈ Ioo (p : ℝ) q, F'.real (env ++ [x]) = F.real (env ++ [x]) :=
    fun x hxI => unitFix F x hxI
  have hLeq : ∀ x ∈ Ioo (p : ℝ) q, x < 0 →
      (if (decide (0 ≤ p) && decide (q ≤ 1)) = true then resolveUnitLog n
        (resolveAxisStep n false F') else resolveAxisStep n false F').real (env ++ [x]) =
        F.real (env ++ [x]) := by
    intro x hxI hneg
    rw [unitFix _ x hxI, (resolveAxisStep_sound (hx x) (by simpa using hneg) F').1, hF'eq x hxI]
  have hReq : ∀ x ∈ Ioo (p : ℝ) q, 0 < x →
      (if (decide (0 ≤ p) && decide (q ≤ 1)) = true then resolveUnitLog n
        (resolveAxisStep n true F') else resolveAxisStep n true F').real (env ++ [x]) =
        F.real (env ++ [x]) := by
    intro x hxI hpos
    rw [unitFix _ x hxI, (resolveAxisStep_sound (hx x) (by simpa using hpos) F').1, hF'eq x hxI]
  have hFc : ∀ x, F.Converges (env ++ [x]) := fun x => noIntegral_converges hF _
  have finish : IntervalIntegrable (fun x => F.real (env ++ [x])) volume p q →
      (∫ x in (p:ℝ)..q, F.real (env ++ [x])) = G.real env →
      (NExpr.integral .interval (.rat p) (.rat q) F).Converges env ∧
        (NExpr.integral .interval (.rat p) (.rat q) F).real env = G.real env := by
    intro hi hv
    exact ⟨⟨trivial, trivial, hi, fun x _ => hFc x⟩, hv⟩
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      obtain ⟨h1, h2⟩ := interval_from_congr hpq'.le rfl rfl hF'eq hG
      exact finish h1 h2.symm
  · split at h
    · simp only [Option.some.injEq] at h
      rename_i hq0
      subst h
      have hq0' : (q : ℝ) ≤ 0 := by exact_mod_cast hq0
      obtain ⟨h1, h2⟩ := interval_from_congr hpq'.le rfl rfl
        (fun x hxI => hLeq x hxI (by linarith [hxI.2])) hG
      exact finish h1 h2.symm
    · split at h
      · simp only [Option.some.injEq] at h
        rename_i hq0 hp0
        subst h
        have hp0' : (0 : ℝ) ≤ p := by exact_mod_cast hp0
        obtain ⟨h1, h2⟩ := interval_from_congr hpq'.le rfl rfl
          (fun x hxI => hReq x hxI (by linarith [hxI.1])) hG
        exact finish h1 h2.symm
      · simp only [Option.some.injEq] at h
        rename_i hq0 hp0
        subst h
        have hq0' : (0 : ℝ) < q := by exact_mod_cast not_le.1 hq0
        have hp0' : (p : ℝ) < 0 := by exact_mod_cast not_le.1 hp0
        rw [add_converges] at hG
        obtain ⟨h1, h2⟩ := interval_from_congr (α := p) (β := 0) hp0'.le rfl (by simp [NExpr.real])
          (fun x hxI => hLeq x ⟨hxI.1, by linarith [hxI.2]⟩ hxI.2) hG.1
        obtain ⟨h3, h4⟩ := interval_from_congr (α := 0) (β := q) hq0'.le (by simp [NExpr.real]) rfl
          (fun x hxI => hReq x ⟨by linarith [hxI.1], hxI.2⟩ hxI.1) hG.2
        refine finish (h1.trans h3) ?_
        rw [add_real, h2, h4, intervalIntegral.integral_add_adjacent_intervals h1 h3]


theorem setIntegral_congr_of_null {f g : ℝ → ℝ} {D S : Set ℝ} (hD : MeasurableSet D)
    (hnull : volume (D \ S) = 0) (h : EqOn f g S) :
    (IntegrableOn f D ↔ IntegrableOn g D) ∧ ∫ x in D, f x = ∫ x in D, g x := by
  have hae : f =ᵐ[volume.restrict D] g := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hD]
    have : ∀ᵐ x ∂volume, x ∉ D \ S := measure_eq_zero_iff_ae_notMem.1 hnull
    filter_upwards [this] with x hx hxD
    exact h (by by_contra hS; exact hx ⟨hxD, hS⟩)
  exact ⟨integrable_congr hae, integral_congr_ae hae⟩

theorem null_two_points {D S : Set ℝ} {a b : ℝ} (h : D \ S ⊆ {a, b}) : volume (D \ S) = 0 :=
  measure_mono_null h ((Set.toFinite _).measure_zero volume)

theorem kind_congr {k : NDomain} {f g : ℝ → ℝ} {α β : ℝ}
    (h : ∀ x ∈ (match k with
        | .right => Set.Ioi α
        | .left => Set.Iio α
        | .whole => Set.univ
        | .interval => Set.uIoo α β
        | _ => Set.Ioo α β), f x = g x) :
    (k.Converges f α β ↔ k.Converges g α β) ∧ k.value f α β = k.value g α β := by
  cases k
  · exact ⟨intervalIntegrable_congr_uIoo h, intervalIntegral.integral_congr_uIoo h⟩
  · exact setIntegral_congr_of_null measurableSet_Icc
      (null_two_points (a := α) (b := β) (fun x hx => by
        simp only [mem_sdiff, mem_Icc, mem_Ioo, not_and_or, not_lt] at hx
        simp only [mem_insert_iff, mem_singleton_iff]
        rcases hx.2 with h1 | h1
        · left; linarith [hx.1.1]
        · right; linarith [hx.1.2])) h
  · exact setIntegral_congr_of_null measurableSet_Ioc
      (null_two_points (a := α) (b := β) (fun x hx => by
        simp only [mem_sdiff, mem_Ioc, mem_Ioo, not_and_or, not_lt] at hx
        simp only [mem_insert_iff, mem_singleton_iff]
        rcases hx.2 with h1 | h1
        · exact absurd hx.1.1 (not_lt.2 h1)
        · right; linarith [hx.1.2])) h
  · exact setIntegral_congr_of_null measurableSet_Ico
      (null_two_points (a := α) (b := β) (fun x hx => by
        simp only [mem_sdiff, mem_Ico, mem_Ioo, not_and_or, not_lt] at hx
        simp only [mem_insert_iff, mem_singleton_iff]
        rcases hx.2 with h1 | h1
        · left; linarith [hx.1.1]
        · exact absurd hx.1.2 (not_lt.2 h1))) h
  · exact setIntegral_congr_of_null measurableSet_Ioo (by simp) h
  · exact setIntegral_congr_of_null measurableSet_Ioi (by simp) h
  · exact setIntegral_congr_of_null measurableSet_Iio (by simp) h
  · have := setIntegral_congr_of_null (D := univ) MeasurableSet.univ (by simp) h
    simp only [integrableOn_univ, Measure.restrict_univ] at this
    exact this

end Intgrl

