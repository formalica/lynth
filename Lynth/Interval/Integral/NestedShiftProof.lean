import Lynth.Interval.Integral.NestedSubstitutionProof

/-! Inserting unused binder levels preserves values and recursive convergence,
including the binders owned by endpoint expressions. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def ShiftEnv (cutoff amount : Nat) (xs ys : List ℝ) : Prop :=
  xs.length + amount = ys.length ∧ cutoff ≤ xs.length ∧
    ∀ i, xs[i]?.getD 0 = ys[if cutoff ≤ i then i+amount else i]?.getD 0

theorem ShiftEnv.push {cutoff amount : Nat} {xs ys : List ℝ}
    (h : ShiftEnv cutoff amount xs ys) (x : ℝ) :
    ShiftEnv cutoff amount (xs++[x]) (ys++[x]) := by
  obtain ⟨hlen,hcut,hget⟩ := h
  refine ⟨by simp; omega,by simp; omega,?_⟩
  intro i
  by_cases hi : i < xs.length
  · have hj : (if cutoff ≤ i then i+amount else i) < ys.length := by
      split <;> omega
    simpa only [List.getElem?_append,hi,hj,↓reduceIte] using hget i
  · by_cases he : i = xs.length
    · subst i
      simp [List.getElem?_append,hcut,← hlen]
    · have hgt : xs.length < i := by omega
      have hci : cutoff ≤ i := by omega
      have hj : ¬i+amount < ys.length := by omega
      have hdiff : i+amount-ys.length ≠ 0 := by omega
      simp [List.getElem?_append,hi,hci,hj,show i-xs.length ≠ 0 by omega,hdiff]

theorem shift_semantics_of_env (e : Expr) {cutoff amount : Nat} {xs ys : List ℝ}
    (h : ShiftEnv cutoff amount xs ys) :
    (e.shift cutoff amount).real ys = e.real xs ∧
      ((e.shift cutoff amount).Converges ys ↔ e.Converges xs) := by
  induction e generalizing xs ys with
  | var i => exact ⟨(h.2.2 i).symm,Iff.rfl⟩
  | rat | pi => exact ⟨rfl,Iff.rfl⟩
  | unary op a ih | pow a n ih | rpow a q ih =>
    obtain ⟨ha,hca⟩ := ih h
    exact ⟨by simp only [NExpr.shift,NExpr.real,ha],hca⟩
  | binary op a b iha ihb =>
    obtain ⟨ha,hca⟩ := iha h
    obtain ⟨hb,hcb⟩ := ihb h
    exact ⟨by simp only [NExpr.shift,NExpr.real,ha,hb],and_congr hca hcb⟩
  | integral k a b f iha ihb ihf =>
    obtain ⟨ha,hca⟩ := iha h
    obtain ⟨hb,hcb⟩ := ihb h
    have hf := fun x => ihf (h.push x)
    have hval : (fun x => (f.shift cutoff amount).real (ys++[x])) =
        (fun x => f.real (xs++[x])) := funext (fun x => (hf x).1)
    constructor
    · simp only [NExpr.shift,NExpr.real,ha,hb,hval]
    · simp only [NExpr.shift,NExpr.Converges,ha,hb,hval]
      exact and_congr hca (and_congr hcb (and_congr Iff.rfl
        (forall_congr' (fun x => forall_congr' (fun _ => (hf x).2)))))

theorem shiftEnv_append (xs zs : List ℝ) :
    ShiftEnv xs.length zs.length xs (xs++zs) := by
  refine ⟨by simp,le_rfl,?_⟩
  intro i
  by_cases hi : i < xs.length
  · simp [List.getElem?_append,hi,show ¬xs.length ≤ i by omega]
  · have hic : xs.length ≤ i := by omega
    have his : xs[i]? = none := List.getElem?_eq_none hic
    have hys : (xs++zs)[i+zs.length]? = none := List.getElem?_eq_none (by simp; omega)
    simp [hic,his,hys]

/-- Unlike the portable value-only transport, this also tracks every inner
integral's ordinary convergence. -/
theorem shift_append_semantics (e : Expr) (xs zs : List ℝ) :
    (e.shift xs.length zs.length).real (xs++zs) = e.real xs ∧
      ((e.shift xs.length zs.length).Converges (xs++zs) ↔ e.Converges xs) :=
  shift_semantics_of_env e (shiftEnv_append xs zs)

theorem endpoint_body_semantics {e : Expr} {xs : List ℝ}
    (hs : e.scoped xs.length = true) (x : ℝ) :
    let E := if e.hasIntegral then e.shift xs.length 1 else e
    E.real (xs++[x]) = e.real xs ∧ (E.Converges (xs++[x]) ↔ e.Converges xs) := by
  dsimp only
  split
  · exact shift_append_semantics e xs [x]
  · rename_i hp
    have hp' : e.hasIntegral = false := by simpa using hp
    exact ⟨pure_append_real hp' hs le_rfl [x],
      iff_of_true (converges_of_noIntegral hp' _) (converges_of_noIntegral hp' _)⟩

end Lynth.Interval.Integral.Nested
