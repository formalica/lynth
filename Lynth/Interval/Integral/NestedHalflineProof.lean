import Lynth.Interval.Integral.NestedPowerProof
import Lynth.Interval.Integral.NestedSubstitutionProof
import Lynth.Interval.Integral.NestedMeasurable

/-! The real change of variables used by canonical half-line memo keys. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def mirror (n : Nat) (e : Expr) : Expr :=
  simplify (e.replace n (sub (.rat 1) (.var n)))

theorem mirror_semantics (e : Expr) (xs : List ℝ) (t : ℝ) :
    (mirror xs.length e).real (xs++[t]) = e.real (xs++[1-t]) ∧
      ((mirror xs.length e).Converges (xs++[t]) ↔ e.Converges (xs++[1-t])) := by
  have hp : PureScoped (xs.length+1) (sub (.rat 1) (.var xs.length)) :=
    sub_pure_scoped (by simp [PureScoped,NExpr.hasIntegral,NExpr.scoped])
      (by simp [PureScoped,NExpr.hasIntegral,NExpr.scoped])
  have hh := replace_semantics e (sub (.rat 1) (.var xs.length)) xs t hp.1 hp.2
  simpa [mirror,(simplify_semantics _).1,(simplify_semantics _).2,
    sub_real,NExpr.real] using hh

def halflineSeed (n : Nat) (right : Bool) (a f : Expr) : Expr :=
  let d := sub (.rat 1) (.var n)
  let u := sub (.unary .inv d) (.rat 1)
  let A := a.shift n 1
  let y := if right then add A u else sub A u
  simplify (div (f.replace n y) (pow d 2))

theorem halflineSeed_semantics (right : Bool) (a f : Expr) (xs : List ℝ) (t : ℝ)
    (hp : a.hasIntegral = false) (hs : a.scoped xs.length = true) :
    let y := if right then a.real xs+(1/(1-t)-1) else a.real xs-(1/(1-t)-1)
    (halflineSeed xs.length right a f).real (xs++[t]) = f.real (xs++[y])/(1-t)^2 ∧
      ((halflineSeed xs.length right a f).Converges (xs++[t]) ↔ f.Converges (xs++[y])) := by
  let d := sub (.rat 1) (.var xs.length)
  let u := sub (.unary .inv d) (.rat 1)
  let A := a.shift xs.length 1
  let y := if right then add A u else sub A u
  have h1 : PureScoped (xs.length+1) (.rat 1) := by simp [PureScoped,NExpr.hasIntegral,NExpr.scoped]
  have hvar : PureScoped (xs.length+1) (.var xs.length) := by
    simp [PureScoped,NExpr.hasIntegral,NExpr.scoped]
  have hd : PureScoped (xs.length+1) d := sub_pure_scoped h1 hvar
  have hu : PureScoped (xs.length+1) u := sub_pure_scoped hd h1
  have hA : PureScoped (xs.length+1) A := by
    rw [show A = a from pure_shift_eq hp hs 1]
    exact ⟨hp,scoped_mono hs (by omega)⟩
  have hy : PureScoped (xs.length+1) y := by
    dsimp only [y]
    split
    · exact add_pure_scoped hA hu
    · exact sub_pure_scoped hA hu
  have hrep := replace_semantics f y xs t hy.1 hy.2
  have ha : A.real (xs++[t]) = a.real xs := by
    rw [show A = a from pure_shift_eq hp hs 1]
    exact pure_append_real hp hs le_rfl [t]
  have hdval : d.real (xs++[t]) = 1-t := by
    simp [d,sub_real,NExpr.real]
  have hyval : y.real (xs++[t]) =
      (if right then a.real xs+(1/(1-t)-1) else a.real xs-(1/(1-t)-1)) := by
    dsimp only [y]
    cases right <;> simp only [Bool.false_eq_true,↓reduceIte,add_real,
      sub_real,u,NExpr.real,Unary.real,ha,hdval,Rat.cast_one,one_div]
  have hden : (pow d 2).Converges (xs++[t]) :=
    (pow_converges d 2 _).mpr (converges_of_noIntegral hd.1 _)
  change (simplify (div (f.replace xs.length y) (pow d 2))).real (xs++[t]) = _ ∧
    ((simplify (div (f.replace xs.length y) (pow d 2))).Converges (xs++[t]) ↔ _)
  rw [(simplify_semantics _).1,(simplify_semantics _).2]
  constructor
  · rw [div_real,pow_real,hdval,hrep.1,hyval]
  · simpa only [div_converges,hden,and_true,hyval] using hrep.2

theorem transformed_halfline_eq (n : Nat) (right : Bool) (a b f : Expr) :
    transformed n (if right then .right else .left) a b f =
      mirror n (regularize n (mirror n (halflineSeed n right a f))) := by
  cases right <;> rfl

theorem transformed_halfline_semantics (right : Bool) (a b f : Expr) (xs : List ℝ) (t : ℝ)
    (hp : a.hasIntegral = false) (hs : a.scoped xs.length = true)
    (ht : t ∈ Set.Ioo (0:ℝ) 1) :
    let E := transformed xs.length (if right then .right else .left) a b f
    let y := if right then a.real xs+t/(1-t) else a.real xs-t/(1-t)
    E.real (xs++[t]) = f.real (xs++[y])/(1-t)^2 ∧
      (E.Converges (xs++[t]) ↔ f.Converges (xs++[y])) := by
  rw [transformed_halfline_eq]
  have hm := mirror_semantics (regularize xs.length (mirror xs.length
    (halflineSeed xs.length right a f))) xs t
  have hr := regularize_semantics xs.length (mirror xs.length (halflineSeed xs.length right a f))
    (xs++[1-t]) (by simpa using sub_pos.mpr ht.2)
  have hi := mirror_semantics (halflineSeed xs.length right a f) xs (1-t)
  have hs := halflineSeed_semantics right a f xs t hp hs
  have ht' : 1-t ≠ 0 := by linarith [ht.2]
  have hy : 1/(1-t)-1 = t/(1-t) := by field_simp; ring
  have he : (1:ℝ)-(1-t) = t := by ring
  rw [he] at hi
  simp only [hy] at hs
  exact ⟨hm.1.trans (hr.1.trans (hi.1.trans hs.1)),hm.2.trans (hr.2.trans (hi.2.trans hs.2))⟩

theorem mobius_surjective {y : ℝ} (hy : 0 < y) :
    ∃ t ∈ Set.Ioo (0:ℝ) 1, t/(1-t) = y := by
  let t := y/(1+y)
  have hd : 0 < 1+y := by linarith
  have ht0 : 0 < t := div_pos hy hd
  have ht1 : t < 1 := (div_lt_one hd).mpr (by linarith)
  refine ⟨t,⟨ht0,ht1⟩,?_⟩
  apply (div_eq_iff (by linarith : 1-t ≠ 0)).mpr
  dsimp [t]
  field_simp [hd.ne']
  ring

theorem halfline_normalization (right : Bool) (a b f : Expr) (xs : List ℝ)
    (hpa : a.hasIntegral = false) (hpb : b.hasIntegral = false)
    (hsa : a.scoped xs.length = true) :
    let k : NDomain := if right then .right else .left
    let original := NExpr.integral k a b f
    let canonical := NExpr.integral .interval (.rat 0) (.rat 1)
      (transformed xs.length (if right then .right else .left) a b f)
    (canonical.Converges xs ↔ original.Converges xs) ∧
      (original.Converges xs → canonical.real xs = original.real xs) := by
  dsimp only
  generalize hE : transformed xs.length (if right then .right else .left) a b f = E
  let k : NDomain := if right then .right else .left
  let F := fun x => f.real (xs++[x])
  let G := fun t : ℝ => E.real (xs++[t])
  let R := fun t : ℝ => F (if right then a.real xs+t/(1-t) else a.real xs-t/(1-t))/(1-t)^2
  let D := if right then Set.Ioi (a.real xs) else Set.Iio (a.real xs)
  have hpoint := transformed_halfline_semantics right a b f xs
  rw [hE] at hpoint
  have heq : (Set.uIoo (0:ℝ) 1).EqOn G R := by
    intro t ht
    have ht' : t ∈ Set.Ioo (0:ℝ) 1 := by simpa only [Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] using ht
    exact (hpoint t hpa hsa ht').1
  have hI : k.Converges F (a.real xs) (b.real xs) ↔
      IntervalIntegrable R MeasureTheory.volume 0 1 := by
    cases right with
    | false => exact left_substitution (f.measurable_body xs)
    | true => exact right_substitution (f.measurable_body xs)
  have hIB : IntervalIntegrable G MeasureTheory.volume 0 1 ↔
      k.Converges F (a.real xs) (b.real xs) :=
    (intervalIntegrable_congr_uIoo heq).trans hI.symm
  have hbody : (∀ t ∈ Set.Ioo (0:ℝ) 1, E.Converges (xs++[t])) ↔
      ∀ x ∈ D, f.Converges (xs++[x]) := by
    constructor
    · intro hh x hx
      cases right with
      | false =>
        have hx' : 0 < a.real xs-x := sub_pos.mpr hx
        obtain ⟨t,ht,he⟩ := mobius_surjective hx'
        have h := (hpoint t hpa hsa ht).2.mp (hh t ht)
        have hy : a.real xs-t/(1-t) = x := by rw [he]; ring
        simpa only [Bool.false_eq_true,↓reduceIte,hy] using h
      | true =>
        have hx' : 0 < x-a.real xs := sub_pos.mpr hx
        obtain ⟨t,ht,he⟩ := mobius_surjective hx'
        have h := (hpoint t hpa hsa ht).2.mp (hh t ht)
        have hy : a.real xs+t/(1-t) = x := by rw [he]; ring
        simpa only [↓reduceIte,hy] using h
    · intro hh t ht
      apply (hpoint t hpa hsa ht).2.mpr
      apply hh
      have hpos : 0 < t/(1-t) := div_pos ht.1 (sub_pos.mpr ht.2)
      cases right <;> simp only [D,Bool.false_eq_true,↓reduceIte,Set.mem_Iio,Set.mem_Ioi] <;> linarith
  have hca := converges_of_noIntegral hpa xs
  have hcb := converges_of_noIntegral hpb xs
  constructor
  · cases right <;>
      simpa only [NExpr.Converges,NExpr.real,NDomain.Converges,k,F,G,D,
        Bool.false_eq_true,↓reduceIte,hca,hcb,true_and,Rat.cast_zero,Rat.cast_one,
        Set.uIoo_of_le (by norm_num : (0:ℝ) ≤ 1)] using and_congr hIB hbody
  · intro hc
    have hi : k.Converges F (a.real xs) (b.real xs) := hc.2.2.1
    have hv : k.value F (a.real xs) (b.real xs) = ∫ t in (0:ℝ)..1, R t := by
      cases right with
      | false => exact left_substitution_value hi
      | true => exact right_substitution_value hi
    simpa only [NExpr.real,NDomain.value,k,F,G,Rat.cast_zero,Rat.cast_one] using
      (intervalIntegral.integral_congr_uIoo heq).trans hv.symm

end Lynth.Interval.Integral.Nested
