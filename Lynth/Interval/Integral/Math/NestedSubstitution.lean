import Lynth.Interval.Integral.Math.NestedDefs

/-! Capture-avoiding operations on absolute binder levels. The definitions
and two semantic obligations depend only on NestedDefs and Mathlib, and are
mirrored in /tmp/intgrl for independent proofs. -/
namespace Intgrl

def NExpr.shift (e : NExpr) (cutoff amount : Nat) : NExpr :=
  match e with
  | .var i => .var (if cutoff ≤ i then i+amount else i)
  | .unary op a => .unary op (a.shift cutoff amount)
  | .binary op a b => .binary op (a.shift cutoff amount) (b.shift cutoff amount)
  | .pow a n => .pow (a.shift cutoff amount) n
  | .rpow a q => .rpow (a.shift cutoff amount) q
  | .integral k a b f => .integral k
      (a.shift cutoff amount) (b.shift cutoff amount) (f.shift cutoff amount)
  | e => e

/-- Replacement terms start in the scope ending at i. Their own binders
must move past each additional binder encountered in the source body. -/
def NExpr.replace (e : NExpr) (i : Nat) (v : NExpr) : NExpr :=
  match e with
  | .var j => if i == j then v else .var j
  | .unary op a => .unary op (a.replace i v)
  | .binary op a b => .binary op (a.replace i v) (b.replace i v)
  | .pow a n => .pow (a.replace i v) n
  | .rpow a q => .rpow (a.replace i v) q
  | .integral k a b f => .integral k (a.replace i v) (b.replace i v)
      (f.replace i (v.shift (i+1) 1))
  | e => e

theorem NExpr.shift_real {e : NExpr} {xs ys : List ℝ}
    (hs : e.scoped xs.length = true) :
    (e.shift xs.length ys.length).real (xs++ys) = e.real xs := by
  have hcore (e : NExpr) : ∀ (xs ys zs : List ℝ),
      (e.shift xs.length ys.length).real (xs ++ ys ++ zs) = e.real (xs ++ zs) := by
      induction e with
      | var i =>
        intro xs ys zs
        simp only [NExpr.real, NExpr.shift]
        rcases lt_or_ge i xs.length with h | h
        · rw [List.append_assoc xs ys zs, if_neg (not_le.2 h),
            List.getElem?_append_left h, List.getElem?_append_left h]
        · rw [List.append_assoc xs ys zs, if_pos h,
            List.getElem?_append_right (by omega : xs.length ≤ i + ys.length),
            List.getElem?_append_right (by omega : ys.length ≤ i + ys.length - xs.length),
            List.getElem?_append_right h,
            show i + ys.length - xs.length - ys.length = i - xs.length by omega]
      | rat q => intro _ _ _; rfl
      | pi => intro _ _ _; rfl
      | unary op a ih => intro xs ys zs; simp only [NExpr.real, NExpr.shift]; rw [ih xs ys zs]
      | binary op a b iha ihb =>
        intro xs ys zs
        simp only [NExpr.real, NExpr.shift]
        rw [iha xs ys zs, ihb xs ys zs]
      | pow a n ih => intro xs ys zs; simp only [NExpr.real, NExpr.shift]; rw [ih xs ys zs]
      | rpow a q ih => intro xs ys zs; simp only [NExpr.real, NExpr.shift]; rw [ih xs ys zs]
      | integral _ a b f iha ihb ihf =>
        intro xs ys zs
        simp only [NExpr.real, NExpr.shift]
        rw [iha xs ys zs, ihb xs ys zs]
        refine NDomain.value_congr _ (fun x => ?_) ?_ ?_
        · rw [List.append_assoc (xs ++ ys) zs [x], ihf xs ys (zs ++ [x]),
            List.append_assoc xs zs [x]]
        · rfl
        · rfl

  have h := hcore e xs ys []
  simp only [List.append_nil] at h
  exact h

theorem NExpr.replace_real {e v : NExpr} {xs : List ℝ}
    (he : e.scoped (xs.length+1) = true) (hv : v.scoped (xs.length+1) = true)
    (t : ℝ) :
    (e.replace xs.length v).real (xs++[t]) =
      e.real (xs++[v.real (xs++[t])]) := by
  have shift_comp (e : NExpr) (c k : ℕ) :
    (e.shift c k).shift c 1 = e.shift c (k + 1)  := by
    induction e with
    | var j =>
      simp only [NExpr.shift]
      rcases lt_or_ge j c with h | h
      · rw [if_neg (not_le.2 h)]
        rw [if_neg (not_le.2 h), if_neg (not_le.2 h)]
      · rw [if_pos h]
        rw [if_pos (by omega : c ≤ j + k), if_pos h]
        simp only [Nat.add_assoc]
    | rat q => rfl
    | pi => rfl
    | unary op a ih => simp only [NExpr.shift]; rw [ih]
    | binary op a b iha ihb => simp only [NExpr.shift]; rw [iha, ihb]
    | pow a m ih => simp only [NExpr.shift]; rw [ih]
    | rpow a q ih => simp only [NExpr.shift]; rw [ih]
    | integral K a b f iha ihb ihf => simp only [NExpr.shift]; rw [iha, ihb, ihf]
  have shift_zero (e : NExpr) (c : ℕ) : e.shift c 0 = e  := by
    induction e with
    | var j =>
      simp only [NExpr.shift]
      rcases lt_or_ge j c with h | h
      · rw [if_neg (not_le.2 h)]
      · rw [if_pos h, Nat.add_zero]
    | rat _ => rfl
    | pi => rfl
    | unary _ _ ih => simp only [NExpr.shift]; rw [ih]
    | binary _ _ _ ihx ihy => simp only [NExpr.shift]; rw [ihx, ihy]
    | pow _ _ iha => simp only [NExpr.shift]; rw [iha]
    | rpow _ _ iha => simp only [NExpr.shift]; rw [iha]
    | integral _ _ _ _ ihx ihy ihf =>
      simp only [NExpr.shift]; rw [ihx, ihy, ihf]
  have shift_env_del (e : NExpr) :
    ∀ (J : ℕ) (σ : List ℝ) (s : ℝ) (P C : List ℝ),
      e.scoped (σ.length + 1 + J) = true →
      (e.shift (σ.length + 1) P.length).real (σ ++ s :: (P ++ C)) =
        e.real (σ ++ s :: C)  := by
    induction e with
    | var j =>
      intro J σ s P C hsc
      simp only [NExpr.real, NExpr.shift]
      rcases lt_or_ge j (σ.length + 1) with h | h
      · rw [if_neg (show ¬(σ.length + 1 ≤ j) by omega)]
        rcases lt_or_ge j σ.length with h2 | h2
        · rw [List.getElem?_append_left h2, List.getElem?_append_left h2]
        · have hje : j = σ.length := by omega
          subst hje
          rw [List.getElem?_append_right (le_refl σ.length),
            List.getElem?_append_right (le_refl σ.length),
            Nat.sub_self, List.getElem?_cons_zero, List.getElem?_cons_zero]
      · rw [if_pos h,
          List.getElem?_append_right (show σ.length ≤ j + P.length by omega),
          show j + P.length - σ.length = (j - σ.length - 1 + P.length) + 1 by omega,
          List.getElem?_cons_succ,
          List.getElem?_append_right (show P.length ≤ j - σ.length - 1 + P.length by omega),
          show j - σ.length - 1 + P.length - P.length = j - σ.length - 1 by omega,
          List.getElem?_append_right (show σ.length ≤ j by omega),
          show j - σ.length = (j - σ.length - 1) + 1 by omega,
          List.getElem?_cons_succ,
          show j - σ.length - 1 + 1 - 1 = j - σ.length - 1 by omega]
    | rat q => intro J σ s P C _; rfl
    | pi => intro J σ s P C _; rfl
    | unary op a ih =>
      intro J σ s P C hsc
      simp only [NExpr.real, NExpr.shift]
      rw [ih J σ s P C hsc]
    | binary op x y ihx ihy =>
      intro J σ s P C hsc
      simp only [NExpr.scoped] at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨hpx, hpy⟩ := hsc
      simp only [NExpr.real, NExpr.shift]
      rw [ihx J σ s P C hpx, ihy J σ s P C hpy]
    | pow a m iha =>
      intro J σ s P C hsc
      simp only [NExpr.real, NExpr.shift]
      rw [iha J σ s P C hsc]
    | rpow a q iha =>
      intro J σ s P C hsc
      simp only [NExpr.real, NExpr.shift]
      rw [iha J σ s P C hsc]
    | integral K x y f ihx ihy ihf =>
      intro J σ s P C hsc
      simp only [NExpr.scoped] at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨hxy, hbf⟩ := hsc
      rw [Bool.and_eq_true] at hxy
      obtain ⟨hpx, hpy⟩ := hxy
      simp only [NExpr.real, NExpr.shift]
      rw [ihx J σ s P C hpx, ihy J σ s P C hpy]
      have hfy : f.scoped (σ.length + 1 + (J + 1)) = true := by
        have hEq : σ.length + 1 + (J + 1) = σ.length + 1 + J + 1 := by omega
        rw [hEq]
        exact hbf
      refine NDomain.value_congr _ (fun z => ?_) ?_ ?_
      · rw [List.append_assoc σ (s :: (P ++ C)) [z], List.cons_append,
          List.append_assoc P C [z],
          List.append_assoc σ (s :: C) [z], List.cons_append]
        exact ihf (J + 1) σ s P (C ++ [z]) hfy
      · rfl
      · rfl
  have replace_env (e : NExpr) (σ : List ℝ) (t : ℝ) (v : NExpr)
    (hv : v.scoped (σ.length + 1) = true) :
    ∀ (β : List ℝ) (d : ℕ), β.length = d →
      e.scoped (σ.length + d + 1) = true →
      (e.replace σ.length (v.shift (σ.length + 1) d)).real (σ ++ t :: β) =
        e.real (σ ++ v.real (σ ++ [t]) :: β)  := by
    induction e with
    | var j =>
      intro β d hβd _
      rcases Nat.lt_trichotomy j σ.length with hj | hj | hj
      · simp only [NExpr.replace]
        rw [if_neg (show ¬((List.length σ == j) = true) by
          rw [beq_iff_eq]
          omega)]
        simp only [NExpr.real]
        rw [List.getElem?_append_left hj, List.getElem?_append_left hj]
      · subst hj
        have hsm : (v.shift (σ.length + 1) d).real (σ ++ t :: β) =
            v.real (σ ++ [t]) := by
          have hEq : σ.length + 1 + 0 = σ.length + 1 := by omega
          have hv0 : v.scoped (σ.length + 1 + 0) = true := by
            rw [hEq]
            exact hv
          have h0 := shift_env_del v 0 σ t β [] hv0
          rw [hβd, List.append_nil] at h0
          exact h0
        simp only [NExpr.replace]
        rw [if_pos (show (List.length σ == List.length σ) = true by simp)]
        simp only [NExpr.real]
        rw [List.getElem?_append_right (le_refl σ.length), Nat.sub_self,
          List.getElem?_cons_zero]
        show (v.shift (σ.length + 1) d).real (σ ++ t :: β) = v.real (σ ++ [t])
        rw [← hsm]
      · simp only [NExpr.replace]
        rw [if_neg (show ¬((List.length σ == j) = true) by
          rw [beq_iff_eq]
          omega)]
        simp only [NExpr.real]
        rw [List.getElem?_append_right (show List.length σ ≤ j by omega),
          List.getElem?_append_right (show List.length σ ≤ j by omega),
          show j - List.length σ = (j - List.length σ - 1) + 1 by omega,
          List.getElem?_cons_succ, List.getElem?_cons_succ]
    | rat _ => intro β d hβd _; simp only [NExpr.replace]; rfl
    | pi => intro β d hβd _; simp only [NExpr.replace]; rfl
    | unary _ _ ih =>
      intro β d hβd hsc
      simp only [NExpr.replace, NExpr.real]
      rw [ih β d hβd hsc]
    | binary _ _ _ ihx ihy =>
      intro β d hβd hsc
      simp only [NExpr.scoped] at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨hpx, hpy⟩ := hsc
      simp only [NExpr.replace, NExpr.real]
      rw [ihx β d hβd hpx, ihy β d hβd hpy]
    | pow _ _ iha =>
      intro β d hβd hsc
      simp only [NExpr.replace, NExpr.real]
      rw [iha β d hβd hsc]
    | rpow _ _ iha =>
      intro β d hβd hsc
      simp only [NExpr.replace, NExpr.real]
      rw [iha β d hβd hsc]
    | integral K a b f ihx ihy ihf =>
      intro β d hβd hsc
      simp only [NExpr.scoped] at hsc
      rw [Bool.and_eq_true] at hsc
      obtain ⟨hxy, hfy⟩ := hsc
      rw [Bool.and_eq_true] at hxy
      obtain ⟨hpx, hpy⟩ := hxy
      simp only [NExpr.replace, NExpr.real]
      rw [shift_comp v (σ.length + 1) d]
      rw [ihx β d hβd hpx, ihy β d hβd hpy]
      have hfyi : f.scoped (σ.length + (d + 1) + 1) = true := by
        have hEq : σ.length + (d + 1) + 1 = σ.length + d + 1 + 1 := by omega
        rw [hEq]
        exact hfy
      refine NDomain.value_congr _ (fun z => ?_) ?_ ?_
      · rw [List.append_assoc σ (t :: β) [z], List.cons_append,
          List.append_assoc σ (v.real (σ ++ [t]) :: β) [z], List.cons_append]
        have hlen : (β ++ [z]).length = d + 1 := by
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        exact ihf (β ++ [z]) (d + 1) hlen hfyi
      · rfl
      · rfl

  have he0 : e.scoped (xs.length + 0 + 1) = true := by
    rw [show xs.length + 0 + 1 = xs.length + 1 by omega]
    exact he
  have h0 := replace_env e xs t v hv ([] : List ℝ) 0 (by rfl) he0
  rw [shift_zero v (xs.length + 1)] at h0
  exact h0
end Intgrl
