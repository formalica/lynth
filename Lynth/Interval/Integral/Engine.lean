import Lynth.Interval.Integral.Search
import Lynth.Interval.Integral.Math.Tails
import Lynth.Interval.Integral.Math.DivergenceRules
import Lynth.Interval.Integral.SyntaxEq

/-! Proper quadrature, explicit tail bounds, and endpoint transformations. -/

namespace Lynth.Interval.Integral

open Intgrl

inductive IntegralCertificate where
  | finite (core : Certificate)
  | tail (cutoff : Dy) (core : Certificate)
  | logarithm (cutoff : Dy) (core : Certificate)
  | sqrtWeight (power : Nat) (core : Certificate)
deriving Repr, Inhabited

def IntegralCertificate.core : IntegralCertificate → Certificate
  | .finite c | .tail _ c | .logarithm _ c | .sqrtWeight _ c => c

def exactPoint (I : Ival) (q : ℚ) : Bool :=
  match I.lo,I.hi with
  | some a,some b => a.toRat == q && b.toRat == q
  | _,_ => false

theorem exactPoint_sound {I : Ival} {q : ℚ} {x : ℝ}
    (hx : x ∈ I) (h : exactPoint I q = true) : x = (q : ℝ) := by
  cases hlo : I.lo with
  | none => simp [exactPoint, hlo] at h
  | some lo =>
    cases hhi : I.hi with
    | none => simp [exactPoint, hlo, hhi] at h
    | some hi =>
      have hh : lo.toRat = q ∧ hi.toRat = q := by simpa [exactPoint, hlo, hhi] using h
      apply le_antisymm
      · simpa only [Dy.toReal_def, hh.2] using hx.2 hi hhi
      · simpa only [Dy.toReal_def, hh.1] using hx.1 lo hlo

def sqrtWeightPower : Term → Option Nat
  | .binary .div (.pow .var n)
      (.unary .sqrt (.binary .sub (.rat q) (.pow .var 2))) =>
      if q == 1 then some n else none
  | _ => none

theorem sqrtWeightPower_sound {e : Term} {n : Nat} (h : sqrtWeightPower e = some n) :
    e = .binary .div (.pow .var n)
      (.unary .sqrt (.binary .sub (.rat 1) (.pow .var 2))) := by
  unfold sqrtWeightPower at h
  split at h
  · split at h <;> simp_all
  · simp at h

def halfPi : Term := .binary .div .pi (.rat 2)
def negHalfPi : Term := .unary .neg halfPi

def tailEncl (c : Ctx) (e A : Term) (kind : Region)
    (R : Dy) (cert : Certificate) : Option Ival := do
  if !R.isPos then none else do
    let model ← classifyTail e
    let err ← (evalR c model.boundTerm (Ival.pt R)).hi
    match kind with
    | .ioi | .ici =>
      if !(Ival.leB (evalR c A Ival.zero) (Ival.pt R)) then none else do
        let core ← finiteEncl c e A (.rat R.toRat) .interval cert
        return Ival.widen c.prec core err
    | .univ =>
      if !model.twoSided then none else do
        let core ← finiteEncl c e (.rat (-R.toRat)) (.rat R.toRat) .interval cert
        return Ival.widen c.prec core (Dy.scale2 err 1)
    | _ => none

def logarithmEncl (c : Ctx) (e A B : Term) (kind : Region)
    (δ : Dy) (cert : Certificate) : Option Ival := do
  if !(e == .unary .log .var && kind.isFinite && exactPoint (evalR c A Ival.zero) 0 &&
      δ.isPos && Dy.leB δ Dy.one && Ival.leB (Ival.pt δ) (evalR c B Ival.zero)) then none else do
    let core ← finiteEncl c e (.rat δ.toRat) B .interval cert
    let bound : Term := .binary .mul .var (.binary .sub (.rat 1) (.unary .log .var))
    let err ← (evalR c bound (Ival.pt δ)).hi
    return Ival.widen c.prec core err

def sqrtWeightEncl (c : Ctx) (e A B : Term) (kind : Region)
    (n : Nat) (cert : Certificate) : Option Ival := do
  if !(sqrtWeightPower e == some n && kind.isFinite &&
      exactPoint (evalR c A Ival.zero) (-1) && exactPoint (evalR c B Ival.zero) 1) then none else
    finiteEncl c (.pow (.unary .sin .var) n) negHalfPi halfPi .interval cert

def integralEncl (c : Ctx) (e A B : Term) (kind : Region)
    (cert : IntegralCertificate) : Option Ival :=
  match cert with
  | .finite core => finiteEncl c e A B kind core
  | .tail R core => tailEncl c e A kind R core
  | .logarithm δ core => logarithmEncl c e A B kind δ core
  | .sqrtWeight n core => sqrtWeightEncl c e A B kind n core

/-- The remaining adapters concern interval encodings and endpoint conventions.
Their premises expose the mathematical tail and main-panel facts separately. -/
def FiniteCoreSound (c : Ctx) (e : Term) (core : Certificate) : Prop :=
  ∀ A B S, finiteEncl c e A B .interval core = some S →
    IntervalIntegrable e.real MeasureTheory.volume (A.real 0) (B.real 0) ∧
      (∫ x in (A.real 0)..(B.real 0), e.real x) ∈ S

theorem finiteCoreSound {c : Ctx} (hc : c.Valid) (e : Term) (core : Certificate) :
    FiniteCoreSound c e core := by
  intro A B S h
  exact finiteEncl_sound hc (Or.inl rfl) h

/-- Lebesgue-null endpoints give the same enclosure for all finite region conventions. -/
theorem finiteRegion_of_Ioo {kind : Region} {f : ℝ → ℝ} {a b : ℝ} {S : Ival}
    (hk : kind.isFinite = true) (hab : a ≤ b)
    (hi : MeasureTheory.IntegrableOn f (Set.Ioo a b))
    (hv : (∫ x in Set.Ioo a b, f x) ∈ S) :
    kind.Converges f a b ∧ kind.value f a b ∈ S := by
  cases kind with
  | interval =>
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mpr hi, ?_⟩
    simpa only [Region.value, intervalIntegral.integral_of_le hab,
      MeasureTheory.integral_Ioc_eq_integral_Ioo] using hv
  | icc =>
    exact ⟨(integrableOn_Icc_iff_integrableOn_Ioo).mpr hi,
      by simpa only [Region.value, Region.set, MeasureTheory.integral_Icc_eq_integral_Ioo] using hv⟩
  | ioc =>
    exact ⟨(integrableOn_Ioc_iff_integrableOn_Ioo).mpr hi,
      by simpa only [Region.value, Region.set, MeasureTheory.integral_Ioc_eq_integral_Ioo] using hv⟩
  | ico =>
    exact ⟨(integrableOn_Ico_iff_integrableOn_Ioo).mpr hi,
      by simpa only [Region.value, Region.set, MeasureTheory.integral_Ico_eq_integral_Ioo] using hv⟩
  | ioo => exact ⟨hi,hv⟩
  | ioi | ici | univ => simp [Region.isFinite] at hk

theorem tailEncl_transport {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {R : Dy} {core : Certificate} {S : Ival}
    (hmain : FiniteCoreSound c e core)
    (htail : ∀ m, classifyTail e = some m → ∀ r : ℝ, 0 < r →
      MeasureTheory.IntegrableOn e.real (Set.Ioi r) ∧
        |(∫ x in Set.Ioi r, e.real x)| ≤ m.boundTerm.real r)
    (hleft : ∀ m, classifyTail e = some m → m.twoSided = true →
      ∀ r : ℝ, 0 < r → MeasureTheory.IntegrableOn e.real (Set.Iio (-r)) ∧
        |(∫ x in Set.Iio (-r), e.real x)| ≤ m.boundTerm.real r)
    (h : tailEncl c e A kind R core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S := by
  unfold tailEncl at h
  split at h
  · simp at h
  · rename_i hR
    have hRpos : 0 < R.toReal := Dy.pos_of_isPos (by simpa using hR)
    cases hm : classifyTail e with
    | none => simp [hm] at h
    | some m =>
      cases he : (evalR c m.boundTerm (Ival.pt R)).hi with
      | none => simp [hm, he] at h
      | some err =>
        have herr : m.boundTerm.real R.toReal ≤ err.toReal :=
          (evalR_sound hc m.boundTerm (Ival.mem_pt R)).2 err he
        have hu := htail m hm R.toReal hRpos
        simp only [hm, he, bind, Option.bind] at h
        cases kind with
        | ioi | ici =>
          dsimp only at h
          split at h
          · simp at h
          · rename_i hle
            have haR : A.real 0 ≤ R.toReal :=
              Ival.le_of_leB (evalR_sound hc A Ival.mem_zero) (Ival.mem_pt R)
                (by simpa using hle)
            cases hs : finiteEncl c e A (.rat R.toRat) .interval core with
            | none => simp [hs] at h
            | some V =>
              have hmain' := hmain A (.rat R.toRat) V hs
              have hh := halfline_assembly haR hmain'.1 hu.1 (hu.2.trans herr)
              have hv : (∫ x in Set.Ioi (A.real 0), e.real x) ∈ S := by
                have heq : Ival.widen c.prec V err = S := by simpa [hs] using h
                rw [← heq]
                exact Ival.mem_widen hmain'.2 hh.2
              first
              | exact ⟨hh.1,hv⟩
              | exact ⟨(integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hh.1,
                  by simpa only [Region.value, Region.set, MeasureTheory.integral_Ici_eq_integral_Ioi] using hv⟩
        | univ =>
          dsimp only at h
          split at h
          · simp at h
          · rename_i htwo
            have hl := hleft m hm (by simpa using htwo) R.toReal hRpos
            cases hs : finiteEncl c e (.rat (-R.toRat)) (.rat R.toRat) .interval core with
            | none => simp [hs] at h
            | some V =>
              have hmain' := hmain (.rat (-R.toRat)) (.rat R.toRat) V hs
              have hh := wholeline_assembly hRpos (by simpa [Term.real, Dy.toReal_def] using hmain'.1) hl.1 hu.1
                (hl.2.trans herr) (hu.2.trans herr)
              have heq : Ival.widen c.prec V (Dy.scale2 err 1) = S := by
                simpa [hs] using h
              refine ⟨hh.1, ?_⟩
              change (∫ x in Set.univ, e.real x) ∈ S
              rw [MeasureTheory.setIntegral_univ, ← heq]
              apply Ival.mem_widen hmain'.2
              convert hh.2 using 1 <;> simp [Term.real, Dy.toReal_def, mul_two]
        | interval | icc | ioc | ico | ioo => simp at h

theorem logarithmEncl_transport {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {δ : Dy} {core : Certificate} {S : Ival}
    (hmain : FiniteCoreSound c e core)
    (hlog : ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      MeasureTheory.IntegrableOn Real.log (Set.Ioo 0 ε) ∧
        |(∫ x in Set.Ioo 0 ε, Real.log x)| = ε * (1 - Real.log ε))
    (h : logarithmEncl c e A B kind δ core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S := by
  unfold logarithmEncl at h
  split at h
  · simp at h
  · rename_i hcheck
    have hh : e = .unary .log .var ∧ kind.isFinite = true ∧
        exactPoint (evalR c A Ival.zero) 0 = true ∧ δ.isPos = true ∧
        Dy.leB δ Dy.one = true ∧ Ival.leB (Ival.pt δ) (evalR c B Ival.zero) = true := by
      simpa only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq,
        and_assoc] using hcheck
    obtain ⟨rfl,hkind,ha,hδ,hδ1,hδB⟩ := hh
    have hA : A.real 0 = 0 := by
      simpa using exactPoint_sound (evalR_sound hc A Ival.mem_zero) ha
    have hd : 0 < δ.toReal := Dy.pos_of_isPos hδ
    have hd1 : δ.toReal ≤ 1 := by simpa [Dy.toReal_def] using Dy.toReal_le_of_leB hδ1
    have hdB : δ.toReal ≤ B.real 0 :=
      Ival.le_of_leB (Ival.mem_pt δ) (evalR_sound hc B Ival.mem_zero) hδB
    cases hs : finiteEncl c (.unary .log .var) (.rat δ.toRat) B .interval core with
    | none => simp [hs] at h
    | some V =>
      let bound : Term := .binary .mul .var (.binary .sub (.rat 1) (.unary .log .var))
      cases he : (evalR c bound (Ival.pt δ)).hi with
      | none =>
        dsimp only [bound] at he
        simp [hs, he] at h
      | some err =>
        have heq : Ival.widen c.prec V err = S := by
          dsimp only [bound] at he
          simpa [hs, he] using h
        have hm := hmain (.rat δ.toRat) B V hs
        have hl := hlog δ.toReal hd hd1
        have hli : IntervalIntegrable Real.log MeasureTheory.volume 0 δ.toReal :=
          (intervalIntegrable_iff_integrableOn_Ioo_of_le hd.le).mpr hl.1
        have hmi : IntervalIntegrable Real.log MeasureTheory.volume δ.toReal (B.real 0) := hm.1
        have hall := hli.trans hmi
        have herr : δ.toReal * (1 - Real.log δ.toReal) ≤ err.toReal :=
          by simpa only [bound, Term.real, Binary.real, Unary.real, Rat.cast_one] using
            (evalR_sound hc bound (Ival.mem_pt δ)).2 err he
        have hv : (∫ x in (0 : ℝ)..B.real 0, Real.log x) ∈ S := by
          rw [← heq]
          apply Ival.mem_widen hm.2
          change |(∫ x in (0 : ℝ)..B.real 0, Real.log x) -
            (∫ x in δ.toReal..B.real 0, Real.log x)| ≤ err.toReal
          have hadd := intervalIntegral.integral_add_adjacent_intervals hli hmi
          rw [← hadd]
          simp only [add_sub_cancel_right]
          simpa only [intervalIntegral.integral_of_le hd.le,
            MeasureTheory.integral_Ioc_eq_integral_Ioo, hl.2] using herr
        rw [hA]
        change kind.Converges Real.log 0 (B.real 0) ∧ kind.value Real.log 0 (B.real 0) ∈ S
        apply finiteRegion_of_Ioo hkind (hd.le.trans hdB)
        · exact (intervalIntegrable_iff_integrableOn_Ioo_of_le (hd.le.trans hdB)).mp hall
        · simpa only [intervalIntegral.integral_of_le (hd.le.trans hdB),
            MeasureTheory.integral_Ioc_eq_integral_Ioo] using hv

theorem sqrtWeightEncl_transport {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {n : Nat} {core : Certificate} {S : Ival}
    (hmain : FiniteCoreSound c (.pow (.unary .sin .var) n) core)
    (hsubst : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ n / Real.sqrt (1 - x ^ 2)) (Set.Ioo (-1) 1) ∧
      (∫ x in Set.Ioo (-1 : ℝ) 1, x ^ n / Real.sqrt (1 - x ^ 2)) =
        ∫ θ in (-Real.pi / 2)..(Real.pi / 2), Real.sin θ ^ n)
    (h : sqrtWeightEncl c e A B kind n core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S := by
  unfold sqrtWeightEncl at h
  split at h
  · simp at h
  · rename_i hcheck
    have hh : sqrtWeightPower e = some n ∧ kind.isFinite = true ∧
        exactPoint (evalR c A Ival.zero) (-1) = true ∧
        exactPoint (evalR c B Ival.zero) 1 = true := by
      simpa only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true, beq_iff_eq,
        and_assoc] using hcheck
    obtain ⟨he,hkind,ha,hb⟩ := hh
    have hA : A.real 0 = -1 := by
      simpa using exactPoint_sound (evalR_sound hc A Ival.mem_zero) ha
    have hB : B.real 0 = 1 := by
      simpa using exactPoint_sound (evalR_sound hc B Ival.mem_zero) hb
    have heq := sqrtWeightPower_sound he
    subst e
    have hm := hmain negHalfPi halfPi S h
    have hv : (∫ x in Set.Ioo (-1 : ℝ) 1, x ^ n / Real.sqrt (1-x^2)) ∈ S := by
      rw [hsubst.2]
      simpa [negHalfPi, halfPi, Term.real, Binary.real, Unary.real, neg_div] using hm.2
    rw [hA,hB]
    simpa [Term.real, Binary.real, Unary.real] using
      finiteRegion_of_Ioo hkind (by norm_num : (-1 : ℝ) ≤ 1) hsubst.1 hv

theorem tailEncl_sound {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {R : Dy} {core : Certificate} {S : Ival}
    (h : tailEncl c e A kind R core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S :=
  tailEncl_transport hc (finiteCoreSound hc e core)
    (fun _ hm _ hr => tailModel_sound hm hr)
    (fun _ hm hs _ hr => tailModel_left_sound hm hs hr) h

theorem logarithmEncl_sound {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {δ : Dy} {core : Certificate} {S : Ival}
    (h : logarithmEncl c e A B kind δ core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S :=
  logarithmEncl_transport hc (finiteCoreSound hc e core)
    (fun _ hp h1 => log_endpoint hp h1) h

theorem sqrtWeightEncl_sound {c : Ctx} (hc : c.Valid) {e A B : Term} {kind : Region}
    {n : Nat} {core : Certificate} {S : Ival}
    (h : sqrtWeightEncl c e A B kind n core = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S :=
  sqrtWeightEncl_transport hc (finiteCoreSound hc _ core)
    (sqrt_weight_substitution (continuous_id.pow n).continuousOn) h

def integralCheck (c : Ctx) (e A B : Term) (kind : Region)
    (cert : IntegralCertificate) (q : ℚ) (tol : Term) : Bool :=
  match cert with
  | .finite core => finiteCheck c e A B kind core q tol
  | _ =>
      match integralEncl c e A B kind cert with
      | some S => closeCheck c S q tol
      | none => false

theorem integralCheck_sound {c : Ctx} (hc : c.Valid) {e A B : Term}
    {kind : Region} {cert : IntegralCertificate} {q : ℚ} {tol : Term}
    (h : integralCheck c e A B kind cert q tol = true) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      |kind.value e.real (A.real 0) (B.real 0) - (q : ℝ)| < tol.real 0 := by
  cases cert with
  | finite core =>
    exact finiteCheck_sound hc h
  | tail R core =>
    cases hs : tailEncl c e A kind R core with
    | none => simp [integralCheck, integralEncl, hs] at h
    | some S =>
      have hh := tailEncl_sound (B := B) hc hs
      exact ⟨hh.1, closeCheck_sound hc hh.2 (by simpa [integralCheck, integralEncl, hs] using h)⟩
  | logarithm δ core =>
    cases hs : logarithmEncl c e A B kind δ core with
    | none => simp [integralCheck, integralEncl, hs] at h
    | some S =>
      have hh := logarithmEncl_sound hc hs
      exact ⟨hh.1, closeCheck_sound hc hh.2 (by simpa [integralCheck, integralEncl, hs] using h)⟩
  | sqrtWeight n core =>
    cases hs : sqrtWeightEncl c e A B kind n core with
    | none => simp [integralCheck, integralEncl, hs] at h
    | some S =>
      have hh := sqrtWeightEncl_sound hc hs
      exact ⟨hh.1, closeCheck_sound hc hh.2 (by simpa [integralCheck, integralEncl, hs] using h)⟩

theorem integration_result_of_check {f : ℝ → ℝ} {a b tol : ℝ}
    {e A B T : Term} {c : Ctx} {kind : Region} {cert : IntegralCertificate} {q : ℚ}
    (hc : c.Valid) (hf : ∀ x, f x = e.real x)
    (ha : a = A.real 0) (hb : b = B.real 0) (htol : tol = T.real 0)
    (h : integralCheck c e A B kind cert q T = true) :
    kind.Converges f a b ∧ |kind.value f a b - (q : ℝ)| < tol := by
  obtain rfl : f = e.real := funext hf
  subst a; subst b; subst tol
  exact integralCheck_sound hc h

def searchIntegralEstimate (c : Ctx) (e A B : Term) (kind : Region)
    (tol : ℚ) (cfg : SearchCfg := {}) : Option (IntegralCertificate × Ival) := Id.run do
  if kind.isFinite then
    if e == .unary .log .var && exactPoint (evalR c A Ival.zero) 0 then
      for bits in [8,16,32,64,128,256,512,1024] do
        let δ : Dy := ⟨1,-(bits : Int)⟩
        let bound : Term := .binary .mul .var (.binary .sub (.rat 1) (.unary .log .var))
        if Ival.ltB (evalR c bound (Ival.pt δ)) (Ival.ofRat c.prec (tol/16)) then
          let some (core,S) := searchFiniteEstimate c e (.rat δ.toRat) B .interval (tol/2) cfg
            | return none
          let some err := (evalR c bound (Ival.pt δ)).hi | return none
          return some (.logarithm δ core,Ival.widen c.prec S err)
      return none
    if let some n := sqrtWeightPower e then
      if exactPoint (evalR c A Ival.zero) (-1) && exactPoint (evalR c B Ival.zero) 1 then
        let some (core,S) := searchFiniteEstimate c (.pow (.unary .sin .var) n)
          negHalfPi halfPi .interval tol cfg | return none
        return some (.sqrtWeight n core,S)
    return (searchFiniteEstimate c e A B kind tol cfg).map fun (core,S) => (.finite core,S)
  let some model := classifyTail e | return none
  if kind == .univ && !model.twoSided then return none
  for exponent in [1:257] do
    let R : Dy := ⟨1,(exponent : Int)⟩
    let err := evalR c model.boundTerm (Ival.pt R)
    if Ival.ltB err (Ival.ofRat c.prec (tol/32)) then
      if kind != .univ && !Ival.leB (evalR c A Ival.zero) (Ival.pt R) then continue
      let AA := if kind == .univ then Term.rat (-R.toRat) else A
      let some (core,S) := searchFiniteEstimate c e AA (.rat R.toRat) .interval (tol/2) cfg
        | return none
      let some err := err.hi | return none
      return some (.tail R core,Ival.widen c.prec S (if kind == .univ then Dy.scale2 err 1 else err))
  return none

def searchIntegral (c : Ctx) (e A B : Term) (kind : Region)
    (tol : ℚ) (cfg : SearchCfg := {}) : Option IntegralCertificate :=
  (searchIntegralEstimate c e A B kind tol cfg).map Prod.fst

end Lynth.Interval.Integral
