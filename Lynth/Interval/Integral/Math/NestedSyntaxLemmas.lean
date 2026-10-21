import Lynth.Interval.Integral.Math.NestedSyntax
import Lynth.Interval.Integral.Math.NestedSyntaxProof

/-! Structural lemmas about the nested expression syntax: lawful equality,
scoping of the syntactic transformations, and their real semantics. -/

namespace Lynth.Interval.Integral.Nested
open Intgrl

/-! ### Scoping -/

theorem shift_scoped {e : Expr} {m : Nat} (c k : Nat) (h : e.scoped m = true) :
    (e.shift c k).scoped (m + k) = true := by
  induction e generalizing m with
  | var i =>
    simp only [NExpr.shift, NExpr.scoped, decide_eq_true_eq] at *
    split <;> omega
  | rat | pi => rfl
  | unary op a ih => exact ih h
  | pow a n ih => exact ih h
  | rpow a q ih => exact ih h
  | binary op a b iha ihb =>
    simp only [NExpr.shift, NExpr.scoped, Bool.and_eq_true] at *
    exact ⟨iha h.1, ihb h.2⟩
  | integral kd a b f iha ihb ihf =>
    simp only [NExpr.shift, NExpr.scoped, Bool.and_eq_true] at *
    refine ⟨⟨iha h.1.1, ihb h.1.2⟩, ?_⟩
    have := ihf h.2
    rwa [show m + 1 + k = m + k + 1 by omega] at this

theorem replace_scoped {e v : Expr} {m : Nat} (i : Nat) (he : e.scoped m = true)
    (hv : v.scoped m = true) : (e.replace i v).scoped m = true := by
  induction e generalizing m v with
  | var j =>
    simp only [NExpr.replace]
    split
    · exact hv
    · exact he
  | rat | pi => rfl
  | unary op a ih => exact ih he hv
  | pow a n ih => exact ih he hv
  | rpow a q ih => exact ih he hv
  | binary op a b iha ihb =>
    simp only [NExpr.replace, NExpr.scoped, Bool.and_eq_true] at *
    exact ⟨iha he.1 hv, ihb he.2 hv⟩
  | integral kd a b f iha ihb ihf =>
    simp only [NExpr.replace, NExpr.scoped, Bool.and_eq_true] at *
    exact ⟨⟨iha he.1.1 hv, ihb he.1.2 hv⟩, ihf he.2 (shift_scoped (i + 1) 1 hv)⟩

theorem scoped_unary {op : Unary} {a : Expr} {m : Nat} :
    (NExpr.unary op a).scoped m = a.scoped m := rfl

theorem scoped_binary {op : Binary} {a b : Expr} {m : Nat} :
    (NExpr.binary op a b).scoped m = (a.scoped m && b.scoped m) := rfl

theorem add_scoped {a b : Expr} {m : Nat} (ha : a.scoped m = true) (hb : b.scoped m = true) :
    (add a b).scoped m = true := by
  unfold add
  split <;> simp_all [NExpr.scoped]

theorem neg_scoped_of {a : Expr} {m : Nat} (ha : a.scoped m = true) :
    (neg a).scoped m = true := by
  unfold neg
  split <;> simp_all [NExpr.scoped]

theorem sub_scoped {a b : Expr} {m : Nat} (ha : a.scoped m = true) (hb : b.scoped m = true) :
    (sub a b).scoped m = true := by
  unfold sub
  split
  · rfl
  · split <;> (try split) <;> (try split) <;> simp_all [NExpr.scoped, neg_scoped_of]

theorem mul_scoped {a b : Expr} {m : Nat} (ha : a.scoped m = true) (hb : b.scoped m = true) :
    (mul a b).scoped m = true := by
  unfold mul
  split <;> (try split) <;> simp_all [NExpr.scoped]

theorem div_scoped {a b : Expr} {m : Nat} (ha : a.scoped m = true) (hb : b.scoped m = true) :
    (div a b).scoped m = true := by
  unfold div
  split <;> simp_all [NExpr.scoped]

theorem pow_scoped {a : Expr} {m : Nat} (n : Nat) (ha : a.scoped m = true) :
    (pow a n).scoped m = true := by
  unfold pow
  split
  · rfl
  · split
    · exact ha
    · split
      · split
        · simp_all [NExpr.scoped]
        · exact neg_scoped_of (by simp_all [NExpr.scoped])
      · simp_all [NExpr.scoped]

theorem rpow_scoped {a : Expr} {m : Nat} (q : ℚ) (ha : a.scoped m = true) :
    (rpow a q).scoped m = true := by
  unfold rpow
  split
  · rfl
  · split
    · exact ha
    · split
      · exact pow_scoped _ ha
      · exact ha

theorem simplify_scoped {e : Expr} {m : Nat} (h : e.scoped m = true) :
    (simplify e).scoped m = true := by
  induction e generalizing m with
  | var | rat | pi => simpa [simplify] using h
  | unary op a ih =>
    cases op <;> simp only [simplify] <;> first
      | exact neg_scoped_of (ih h)
      | exact ih h
  | binary op a b iha ihb =>
    simp only [NExpr.scoped, Bool.and_eq_true] at h
    cases op <;> simp only [simplify]
    · exact add_scoped (iha h.1) (ihb h.2)
    · exact sub_scoped (iha h.1) (ihb h.2)
    · exact mul_scoped (iha h.1) (ihb h.2)
    · exact div_scoped (iha h.1) (ihb h.2)
    · simp [NExpr.scoped, iha h.1, ihb h.2]
    · simp [NExpr.scoped, iha h.1, ihb h.2]
  | pow a n ih => exact pow_scoped n (ih h)
  | rpow a q ih => exact rpow_scoped q (ih h)
  | integral k a b f iha ihb ihf =>
    simp only [NExpr.scoped, Bool.and_eq_true, simplify] at *
    exact ⟨⟨iha h.1.1, ihb h.1.2⟩, ihf h.2⟩

theorem collectPower_scoped {e : Expr} {m : Nat} (level : Nat) (hl : level < m)
    (h : e.scoped m = true) : (collectPower level e).2.scoped m = true := by
  have hv : (NExpr.var level).scoped m = true := by simpa [NExpr.scoped] using hl
  induction e generalizing m with
  | var i =>
    simp only [collectPower]
    split <;> simp_all [NExpr.scoped]
  | rat | pi => simpa [collectPower] using h
  | unary op a ih =>
    cases op <;> simp only [collectPower] <;> first
      | exact neg_scoped_of (ih hl h hv)
      | exact ih hl h hv
      | exact h
  | binary op a b iha ihb =>
    have h' := h
    simp only [NExpr.scoped, Bool.and_eq_true] at h'
    have hA := iha hl h'.1 hv
    have hB := ihb hl h'.2 hv
    cases op <;> simp only [collectPower]
    · exact add_scoped (mul_scoped (rpow_scoped _ hv) hA) (mul_scoped (rpow_scoped _ hv) hB)
    · exact sub_scoped (mul_scoped (rpow_scoped _ hv) hA) (mul_scoped (rpow_scoped _ hv) hB)
    · exact mul_scoped hA hB
    · exact div_scoped hA hB
    · exact h
    · exact h
  | pow a n ih => exact pow_scoped n (ih hl h hv)
  | rpow a q ih => exact h
  | integral k a b f iha ihb ihf => exact h

theorem regularize_scoped {e : Expr} {m : Nat} (level : Nat) (hl : level < m)
    (h : e.scoped m = true) : (regularize level e).scoped m = true := by
  have hv : (NExpr.var level).scoped m = true := by simpa [NExpr.scoped] using hl
  unfold regularize
  exact simplify_scoped (mul_scoped (rpow_scoped _ hv)
    (collectPower_scoped level hl (simplify_scoped h)))

theorem scoped_of_not_uses {e : Expr} {n : Nat} (h : e.scoped (n + 1) = true)
    (hu : e.uses n = false) (hi : e.hasIntegral = false) : e.scoped n = true := by
  induction e with
  | var i =>
    simp only [NExpr.scoped, NExpr.uses, decide_eq_true_eq, beq_eq_false_iff_ne] at *
    omega
  | rat | pi => rfl
  | unary op a ih => exact ih h hu hi
  | pow a k ih => exact ih h hu hi
  | rpow a q ih => exact ih h hu hi
  | binary op a b iha ihb =>
    simp only [NExpr.scoped, NExpr.uses, NExpr.hasIntegral, Bool.and_eq_true,
      Bool.or_eq_false_iff] at *
    exact ⟨iha h.1 hu.1 hi.1, ihb h.2 hu.2 hi.2⟩
  | integral => simp [NExpr.hasIntegral] at hi

end Lynth.Interval.Integral.Nested

/-! ### Real semantics of the simplifiers -/

namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem noIntegral_converges {e : Expr} (h : e.hasIntegral = false) (env : List ℝ) :
    e.Converges env := by
  induction e with
  | var | rat | pi => trivial
  | unary op e ih | pow e n ih | rpow e q ih => exact ih h
  | binary op e f ihe ihf =>
      have hh := Bool.or_eq_false_iff.mp h
      exact ⟨ihe hh.1, ihf hh.2⟩
  | integral => simp [NExpr.hasIntegral] at h

theorem simplify_sound (e : Expr) (env : List ℝ) :
    (simplify e).real env = e.real env ∧ ((simplify e).Converges env ↔ e.Converges env) := by
  induction e generalizing env with
  | var | rat | pi => simp [simplify]
  | unary op a ih =>
    cases op <;> simp only [simplify]
    case neg => exact ⟨by rw [neg_real, (ih env).1]; rfl, by rw [neg_converges]; exact (ih env).2⟩
    all_goals exact ⟨by simp only [NExpr.real]; rw [(ih env).1], (ih env).2⟩
  | binary op a b iha ihb =>
    cases op <;> simp only [simplify]
    · exact ⟨by rw [add_real, (iha env).1, (ihb env).1]; rfl,
        by rw [add_converges, (iha env).2, (ihb env).2]; rfl⟩
    · exact ⟨by rw [sub_real, (iha env).1, (ihb env).1]; rfl,
        by rw [sub_converges, (iha env).2, (ihb env).2]; rfl⟩
    · exact ⟨by rw [mul_real, (iha env).1, (ihb env).1]; rfl,
        by rw [mul_converges, (iha env).2, (ihb env).2]; rfl⟩
    · exact ⟨by rw [div_real, (iha env).1, (ihb env).1]; rfl,
        by rw [div_converges, (iha env).2, (ihb env).2]; rfl⟩
    · exact ⟨by simp only [NExpr.real]; rw [(iha env).1, (ihb env).1],
        by simp only [NExpr.Converges]; rw [(iha env).2, (ihb env).2]⟩
    · exact ⟨by simp only [NExpr.real]; rw [(iha env).1, (ihb env).1],
        by simp only [NExpr.Converges]; rw [(iha env).2, (ihb env).2]⟩
  | pow a n ih =>
    simp only [simplify]
    exact ⟨by rw [pow_real, (ih env).1]; rfl, by rw [pow_converges]; exact (ih env).2⟩
  | rpow a q ih =>
    simp only [simplify]
    exact ⟨by rw [rpow_real, (ih env).1]; rfl, by rw [rpow_converges]; exact (ih env).2⟩
  | integral k a b f iha ihb ihf =>
    have hf : (fun x => (simplify f).real (env ++ [x])) = fun x => f.real (env ++ [x]) :=
      funext fun x => (ihf _).1
    refine ⟨?_, ?_⟩
    · simp only [simplify, NExpr.real]
      rw [hf, (iha env).1, (ihb env).1]
    · simp only [simplify, NExpr.Converges]
      rw [hf, (iha env).1, (ihb env).1, (iha env).2, (ihb env).2]
      simp only [fun x => (ihf (env ++ [x])).2]

end Lynth.Interval.Integral.Nested

/-! ### Semantics of binder shifts and substitution -/

namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem getElem?_shift_insert {L1 L2 : List ℝ} {c : Nat} (hc : L1.length = c) (t : ℝ) (i : Nat) :
    (L1 ++ t :: L2)[(if c ≤ i then i + 1 else i)]? = (L1 ++ L2)[i]? := by
  split
  · rename_i h
    rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
    rw [show i + 1 - L1.length = (i - L1.length) + 1 by omega]
    simp
  · rename_i h
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

theorem shift_sound (e : Expr) {c : Nat} {L1 : List ℝ} (hc : L1.length = c) (t : ℝ)
    (L2 : List ℝ) :
    (e.shift c 1).real (L1 ++ t :: L2) = e.real (L1 ++ L2) ∧
      ((e.shift c 1).Converges (L1 ++ t :: L2) ↔ e.Converges (L1 ++ L2)) := by
  induction e generalizing L2 with
  | var i =>
    simp only [NExpr.shift, NExpr.real, NExpr.Converges, and_true]
    rw [getElem?_shift_insert hc]
  | rat | pi => simp [NExpr.shift, NExpr.real, NExpr.Converges]
  | unary op a ih =>
    simp only [NExpr.shift, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih L2).1], (ih L2).2⟩
  | pow a n ih =>
    simp only [NExpr.shift, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih L2).1], (ih L2).2⟩
  | rpow a q ih =>
    simp only [NExpr.shift, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih L2).1], (ih L2).2⟩
  | binary op a b iha ihb =>
    simp only [NExpr.shift, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(iha L2).1, (ihb L2).1], by rw [(iha L2).2, (ihb L2).2]⟩
  | integral k a b f iha ihb ihf =>
    have hf : ∀ x, (f.shift c 1).real ((L1 ++ t :: L2) ++ [x]) = f.real ((L1 ++ L2) ++ [x]) := by
      intro x
      have := (ihf (L2 ++ [x])).1
      simpa using this
    have hfc : ∀ x, (f.shift c 1).Converges ((L1 ++ t :: L2) ++ [x]) ↔
        f.Converges ((L1 ++ L2) ++ [x]) := by
      intro x
      have := (ihf (L2 ++ [x])).2
      simpa using this
    simp only [NExpr.shift, NExpr.real, NExpr.Converges]
    refine ⟨?_, ?_⟩
    · rw [(iha L2).1, (ihb L2).1]
      simp only [hf]
    · rw [(iha L2).1, (ihb L2).1, (iha L2).2, (ihb L2).2]
      simp only [hf, hfc]

theorem replace_sound (e : Expr) {i : Nat} {E0 : List ℝ} (hE : E0.length = i + 1) (cval : ℝ)
    (u : Expr) (L : List ℝ) (hu : ∀ L' : List ℝ, L'.length = L.length → u.real (E0 ++ L') = cval) :
    (e.replace i u).real (E0 ++ L) = e.real ((E0 ++ L).set i cval) ∧
      ((e.replace i u).Converges (E0 ++ L) → e.Converges ((E0 ++ L).set i cval)) := by
  induction e generalizing u L with
  | var j =>
    simp only [NExpr.replace]
    split
    · rename_i h
      have hj : i = j := by simpa using h
      subst hj
      refine ⟨?_, fun _ => trivial⟩
      rw [hu L rfl]
      simp only [NExpr.real]
      rw [List.getElem?_set_self (by simp [hE]; omega)]
      rfl
    · rename_i h
      have hj : i ≠ j := by simpa using h
      refine ⟨?_, fun _ => trivial⟩
      simp only [NExpr.real]
      rw [List.getElem?_set_ne hj]
  | rat | pi => simp [NExpr.replace, NExpr.real, NExpr.Converges]
  | unary op a ih =>
    simp only [NExpr.replace, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih u L hu).1], (ih u L hu).2⟩
  | pow a n ih =>
    simp only [NExpr.replace, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih u L hu).1], (ih u L hu).2⟩
  | rpow a q ih =>
    simp only [NExpr.replace, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(ih u L hu).1], (ih u L hu).2⟩
  | binary op a b iha ihb =>
    simp only [NExpr.replace, NExpr.real, NExpr.Converges]
    exact ⟨by rw [(iha u L hu).1, (ihb u L hu).1],
      fun h => ⟨(iha u L hu).2 h.1, (ihb u L hu).2 h.2⟩⟩
  | integral k a b f iha ihb ihf =>
    have hu' : ∀ x : ℝ, ∀ L' : List ℝ, L'.length = (L ++ [x]).length →
        (u.shift (i + 1) 1).real (E0 ++ L') = cval := by
      intro x L' hL'
      match L', hL' with
      | [], h => simp at h
      | y :: rest, hL' =>
        rw [(shift_sound u hE y rest).1]
        exact hu rest (by simp at hL'; omega)
    have hset : ∀ x : ℝ, (E0 ++ L ++ [x]).set i cval = (E0 ++ L).set i cval ++ [x] := by
      intro x
      rw [List.set_append_left _ _ (by simp [hE]; omega)]
    have hf : ∀ x, (f.replace i (u.shift (i + 1) 1)).real ((E0 ++ L) ++ [x]) =
        f.real ((E0 ++ L).set i cval ++ [x]) := by
      intro x
      have := (ihf (u.shift (i + 1) 1) (L ++ [x]) (hu' x)).1
      rw [← hset x]
      simpa only [List.append_assoc] using this
    have hfc : ∀ x, (f.replace i (u.shift (i + 1) 1)).Converges ((E0 ++ L) ++ [x]) →
        f.Converges ((E0 ++ L).set i cval ++ [x]) := by
      intro x hx
      have := (ihf (u.shift (i + 1) 1) (L ++ [x]) (hu' x)).2
      rw [← hset x]
      simp only [List.append_assoc] at this hx ⊢
      exact this hx
    simp only [NExpr.replace, NExpr.real, NExpr.Converges]
    refine ⟨?_, ?_⟩
    · rw [(iha u L hu).1, (ihb u L hu).1]
      simp only [hf]
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨(iha u L hu).2 h1, (ihb u L hu).2 h2, ?_, ?_⟩
      · rw [← (iha u L hu).1, ← (ihb u L hu).1]
        simp only [← hf]
        exact h3
      · rw [← (iha u L hu).1, ← (ihb u L hu).1]
        intro x hx
        exact hfc x (h4 x hx)

end Lynth.Interval.Integral.Nested

