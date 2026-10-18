import Lynth.Interval.Integral.NestedSemantics

/-! Binder transport of values and recursive ordinary convergence. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

theorem pure_uses_lt {e : Expr} (hp : e.hasIntegral = false) {n : Nat}
    (hs : e.scoped n = true) {i : Nat} (hu : e.uses i = true) : i < n := by
  induction e with
  | var j =>
    have hij : i = j := by simpa [NExpr.uses] using hu
    subst j
    simpa [NExpr.scoped] using hs
  | rat | pi => simp [NExpr.uses] at hu
  | unary op a ih | pow a k ih | rpow a q ih => exact ih hp hs hu
  | binary op a b iha ihb =>
    have hps := Bool.or_eq_false_iff.mp hp
    have hss := Bool.and_eq_true_iff.mp hs
    rcases Bool.or_eq_true_iff.mp hu with hu | hu
    · exact iha hps.1 hss.1 hu
    · exact ihb hps.2 hss.2 hu
  | integral => simp [NExpr.hasIntegral] at hp

theorem pure_env_congr {e : Expr} (hp : e.hasIntegral = false) {xs ys : List ℝ}
    (hu : ∀ i, e.uses i = true → xs[i]?.getD 0 = ys[i]?.getD 0) :
    e.real xs = e.real ys := by
  induction e with
  | var i => exact hu i (by simp [NExpr.uses])
  | rat | pi => rfl
  | unary op a ih | pow a n ih | rpow a q ih =>
    simp only [NExpr.real,ih hp hu]
  | binary op a b iha ihb =>
    have hps := Bool.or_eq_false_iff.mp hp
    have ha := iha hps.1 (fun i hi => hu i (by simp [NExpr.uses,hi]))
    have hb := ihb hps.2 (fun i hi => hu i (by simp [NExpr.uses,hi]))
    simp only [NExpr.real,ha,hb]
  | integral => simp [NExpr.hasIntegral] at hp

theorem pure_append_real {e : Expr} (hp : e.hasIntegral = false) {n : Nat}
    (hs : e.scoped n = true) {xs : List ℝ} (hlen : n ≤ xs.length) (ys : List ℝ) :
    e.real (xs++ys) = e.real xs := by
  apply pure_env_congr hp
  intro i hi
  have hib : i < xs.length := (pure_uses_lt hp hs hi).trans_le hlen
  simp [List.getElem?_append,hib]

theorem pure_shift_eq {e : Expr} (hp : e.hasIntegral = false) {n : Nat}
    (hs : e.scoped n = true) (amount : Nat) : e.shift n amount = e := by
  induction e with
  | var i =>
    have hi : i < n := by simpa [NExpr.scoped] using hs
    simp [NExpr.shift,show ¬n ≤ i by omega]
  | rat | pi => rfl
  | unary op a ih | pow a k ih | rpow a q ih => simp only [NExpr.shift,ih hp hs]
  | binary op a b iha ihb =>
    have hps := Bool.or_eq_false_iff.mp hp
    have hss := Bool.and_eq_true_iff.mp hs
    simp only [NExpr.shift,iha hps.1 hss.1,ihb hps.2 hss.2]
  | integral => simp [NExpr.hasIntegral] at hp

theorem neg_hasIntegral (a : Expr) : (neg a).hasIntegral = a.hasIntegral := by
  fun_cases neg a <;> simp [NExpr.hasIntegral]

theorem neg_scoped (a : Expr) (n : Nat) : (neg a).scoped n = a.scoped n := by
  fun_cases neg a <;> simp [NExpr.scoped]

theorem scoped_mono {e : Expr} {n m : Nat} (hs : e.scoped n = true) (hnm : n ≤ m) :
    e.scoped m = true := by
  induction e generalizing n m with
  | var i =>
    have hi : i < n := by simpa [NExpr.scoped] using hs
    simpa [NExpr.scoped] using hi.trans_le hnm
  | rat | pi => rfl
  | unary op a ih | pow a k ih | rpow a q ih => exact ih hs hnm
  | binary op a b iha ihb =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hs
    exact Bool.and_eq_true_iff.mpr ⟨iha ha hnm,ihb hb hnm⟩
  | integral k a b f iha ihb ihf =>
    obtain ⟨hab,hf⟩ := Bool.and_eq_true_iff.mp hs
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp hab
    exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr ⟨iha ha hnm,ihb hb hnm⟩,
      ihf hf (by omega)⟩

def PureScoped (n : Nat) (e : Expr) : Prop := e.hasIntegral = false ∧ e.scoped n = true

theorem neg_pure_scoped {n : Nat} {a : Expr} (ha : PureScoped n a) : PureScoped n (neg a) := by
  rcases ha with ⟨hp,hs⟩
  fun_cases neg a <;> simp_all [PureScoped,NExpr.hasIntegral,NExpr.scoped]

theorem add_pure_scoped {n : Nat} {a b : Expr} (ha : PureScoped n a) (hb : PureScoped n b) :
    PureScoped n (add a b) := by
  rcases ha with ⟨hpa,hsa⟩
  rcases hb with ⟨hpb,hsb⟩
  fun_cases add a b <;> simp_all [PureScoped,NExpr.hasIntegral,NExpr.scoped]

theorem sub_pure_scoped {n : Nat} {a b : Expr} (ha : PureScoped n a) (hb : PureScoped n b) :
    PureScoped n (sub a b) := by
  rcases ha with ⟨hpa,hsa⟩
  rcases hb with ⟨hpb,hsb⟩
  fun_cases sub a b <;> simp only [PureScoped,NExpr.hasIntegral,NExpr.scoped,
    neg_hasIntegral,neg_scoped,Bool.or_eq_false_iff,Bool.and_eq_true,and_true,true_and,and_self] at *
  all_goals aesop (config := {enableSimp := false})

theorem mul_pure_scoped {n : Nat} {a b : Expr} (ha : PureScoped n a) (hb : PureScoped n b) :
    PureScoped n (mul a b) := by
  rcases ha with ⟨hpa,hsa⟩
  rcases hb with ⟨hpb,hsb⟩
  fun_cases mul a b <;> simp_all [PureScoped,NExpr.hasIntegral,NExpr.scoped]

theorem div_pure_scoped {n : Nat} {a b : Expr} (ha : PureScoped n a) (hb : PureScoped n b) :
    PureScoped n (div a b) := by
  rcases ha with ⟨hpa,hsa⟩
  rcases hb with ⟨hpb,hsb⟩
  fun_cases div a b <;> simp_all [PureScoped,NExpr.hasIntegral,NExpr.scoped]

theorem pow_pure_scoped {n : Nat} {a : Expr} (ha : PureScoped n a) (k : Nat) :
    PureScoped n (pow a k) := by
  rcases ha with ⟨hp,hs⟩
  fun_cases pow a k <;> simp only [PureScoped,NExpr.hasIntegral,NExpr.scoped,
    neg_hasIntegral,neg_scoped,and_true,true_and,and_self] at *
  all_goals aesop (config := {enableSimp := false})

def SubstEnv (i : Nat) (v : Expr) (xs ys : List ℝ) : Prop :=
  xs.length = ys.length ∧ i < xs.length ∧ ys[i]?.getD 0 = v.real xs ∧
    ∀ j, j ≠ i → xs[j]?.getD 0 = ys[j]?.getD 0

theorem SubstEnv.push {i : Nat} {v : Expr} (hp : v.hasIntegral = false)
    (hs : v.scoped (i+1) = true) {xs ys : List ℝ} (h : SubstEnv i v xs ys) (x : ℝ) :
    SubstEnv i v (xs++[x]) (ys++[x]) := by
  have hi := h.2.1
  have hiy : i < ys.length := h.1 ▸ hi
  refine ⟨by simp [h.1],by simp; omega,?_,?_⟩
  · rw [pure_append_real hp hs (by omega)]
    simpa only [List.getElem?_append,hi,hiy,↓reduceIte] using h.2.2.1
  · intro j hj
    by_cases hi : j < xs.length
    · have hi' : j < ys.length := h.1 ▸ hi
      simpa only [List.getElem?_append,hi,hi',↓reduceIte] using h.2.2.2 j hj
    · have hi' : ¬j < ys.length := h.1 ▸ hi
      simp [List.getElem?_append,hi,hi',h.1]

theorem replace_semantics_of_env (e : Expr) {i : Nat} {v : Expr}
    (hp : v.hasIntegral = false) (hs : v.scoped (i+1) = true)
    {xs ys : List ℝ} (h : SubstEnv i v xs ys) :
    (e.replace i v).real xs = e.real ys ∧
      ((e.replace i v).Converges xs ↔ e.Converges ys) := by
  induction e generalizing xs ys with
  | var j =>
    simp only [NExpr.replace]
    split
    · rename_i hij
      have he : i = j := by simpa using hij
      subst j
      exact ⟨h.2.2.1.symm,by simpa [NExpr.Converges] using converges_of_noIntegral hp xs⟩
    · rename_i hij
      have he : j ≠ i := by simpa [ne_comm] using hij
      exact ⟨h.2.2.2 j he,Iff.rfl⟩
  | rat | pi => exact ⟨rfl,Iff.rfl⟩
  | unary op a ih | pow a n ih | rpow a q ih =>
    obtain ⟨ha,hca⟩ := ih h
    exact ⟨by simp only [NExpr.replace,NExpr.real,ha],hca⟩
  | binary op a b iha ihb =>
    obtain ⟨ha,hca⟩ := iha h
    obtain ⟨hb,hcb⟩ := ihb h
    exact ⟨by simp only [NExpr.replace,NExpr.real,ha,hb],and_congr hca hcb⟩
  | integral k a b f iha ihb ihf =>
    obtain ⟨ha,hca⟩ := iha h
    obtain ⟨hb,hcb⟩ := ihb h
    have hf := fun x => ihf (h.push hp hs x)
    have hval : (fun x => (f.replace i v).real (xs++[x])) =
        (fun x => f.real (ys++[x])) := funext (fun x => (hf x).1)
    constructor
    · simp only [NExpr.replace,NExpr.real,pure_shift_eq hp hs,ha,hb,hval]
    · simp only [NExpr.replace,NExpr.Converges,pure_shift_eq hp hs,ha,hb,hval]
      exact and_congr hca (and_congr hcb (and_congr Iff.rfl
        (forall_congr' (fun x => forall_congr' (fun _ => (hf x).2)))))

theorem replace_semantics (e v : Expr) (xs : List ℝ) (t : ℝ)
    (hp : v.hasIntegral = false) (hs : v.scoped (xs.length+1) = true) :
    (e.replace xs.length v).real (xs++[t]) = e.real (xs++[v.real (xs++[t])]) ∧
      ((e.replace xs.length v).Converges (xs++[t]) ↔
        e.Converges (xs++[v.real (xs++[t])])) := by
  apply replace_semantics_of_env e hp hs
  refine ⟨by simp,by simp,by simp,?_⟩
  intro j hj
  by_cases hi : j < xs.length
  · simp [List.getElem?_append,hi]
  · have hgt : xs.length < j := by omega
    simp [List.getElem?_append,hi,show j-xs.length ≠ 0 by omega]

end Lynth.Interval.Integral.Nested
