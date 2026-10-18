import Lynth.Interval.Integral.Legendre

/-! Correctness of the rectangular polynomial evaluation loops. -/
namespace Lynth.Interval.Integral
open scoped BigOperators

theorem forIn_ite_yield_eq_foldl {α β : Type} (xs : List α) (init : β)
    (P : α → Prop) [DecidablePred P] (f : α → β → β) :
    (forIn xs init (fun a b => if P a then pure (ForInStep.yield (f a b))
      else pure (ForInStep.yield b)) : Id β) =
      pure (xs.foldl (fun b a => if P a then f a b else b) init) := by
  have hf : (fun a b => if P a then pure (ForInStep.yield (f a b))
      else pure (ForInStep.yield b)) =
      (fun a b => (pure (ForInStep.yield (if P a then f a b else b)) : Id (ForInStep β))) := by
    funext a b
    split <;> rfl
  rw [hf,List.forIn_pure_yield_eq_foldl]

theorem sum_range_blocks (f : Nat → ℝ) (n b : Nat) :
    (∑ i ∈ Finset.range (n*b), f i) =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range b, f (i*b+j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem rect_powers {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (n : Nat) :
    let powers := (List.range n).foldl (fun ps _ => ps.push (Ival.mul p ps.back! X)) #[Ival.one]
    powers.size = n+1 ∧ ∀ i, i ≤ n → x^i ∈ powers[i]! := by
  induction n with
  | zero => simp [Ival.mem_one]
  | succ n ih =>
    dsimp only at ih ⊢
    rw [List.range_succ,List.foldl_append]
    dsimp only [List.foldl]
    let P := (List.range n).foldl (fun ps _ => ps.push (Ival.mul p ps.back! X)) #[Ival.one]
    change P.size = n+1 ∧ ∀ i, i ≤ n → x^i ∈ P[i]! at ih
    obtain ⟨hlen,hpow⟩ := ih
    change (P.push (Ival.mul p P.back! X)).size = n+1+1 ∧
      ∀ i, i ≤ n+1 → x^i ∈ (P.push (Ival.mul p P.back! X))[i]!
    refine ⟨by simp [hlen],?_⟩
    intro i hi
    have hip : i < (P.push (Ival.mul p P.back! X)).size := by simp [hlen]; omega
    by_cases hin : i ≤ n
    · have hib : i < P.size := by omega
      simpa only [getElem!_pos (P.push (Ival.mul p P.back! X)) i hip,Array.getElem_push_lt hib,
        ← getElem!_pos P i hib] using hpow i hin
    · have hie : i = n+1 := by omega
      subst i
      have hget : (P.push (Ival.mul p P.back! X))[n+1]! = Ival.mul p P[n]! X := by
        rw [getElem!_pos (P.push (Ival.mul p P.back! X)) (n+1) hip]
        have he : n+1 = P.size := hlen.symm
        simp only [he,Array.getElem_push_eq]
        simp [Array.back!,hlen]
      rw [hget,pow_succ]
      exact Ival.mem_mul (hpow n le_rfl) hx

theorem rect_inner {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X)
    (coeff : Array Int) (powers : Array Ival) (block k : Nat)
    (hp : ∀ i, i ≤ block → x^i ∈ powers[i]!) :
    ∀ m ≤ block,
      (∑ j ∈ Finset.range m,
        if k*block+j < coeff.size then (coeff[k*block+j]! : ℝ)*x^j else 0) ∈
      (List.range m).foldl (fun v j =>
        if k*block+j < coeff.size then
          Ival.add p v (Ival.mul p (Ival.pt (Dy.ofInt coeff[k*block+j]!)) powers[j]!)
        else v) Ival.zero := by
  intro m hm
  induction m with
  | zero => simpa using Ival.mem_zero
  | succ m ih =>
    rw [Finset.sum_range_succ,List.range_succ,List.foldl_append]
    dsimp only [List.foldl]
    split
    · have hcoef : (coeff[k*block+m]! : ℝ) ∈ Ival.pt (Dy.ofInt coeff[k*block+m]!) := by
        simpa [Dy.toReal_def] using Ival.mem_pt (Dy.ofInt coeff[k*block+m]!)
      exact Ival.mem_add (ih (by omega)) (Ival.mem_mul hcoef (hp m (by omega)))
    · simpa using ih (by omega)

noncomputable def rectBlock (coeff : Array Int) (x : ℝ) (block k : Nat) : ℝ :=
  ∑ j ∈ Finset.range block,
    if k*block+j < coeff.size then (coeff[k*block+j]! : ℝ)*x^j else 0

noncomputable def rectPrefix (coeff : Array Int) (x : ℝ) (block blocks m : Nat) : ℝ :=
  ∑ i ∈ Finset.range m, x^(i*block)*rectBlock coeff x block (blocks-m+i)

theorem rectPrefix_step (coeff : Array Int) (x : ℝ) (block blocks m : Nat) (hm : m < blocks) :
    rectPrefix coeff x block blocks (m+1) =
      rectPrefix coeff x block blocks m*x^block + rectBlock coeff x block (blocks-1-m) := by
  unfold rectPrefix
  rw [Finset.sum_range_succ',Finset.sum_mul]
  simp only [Nat.zero_mul,pow_zero,one_mul,Nat.add_zero]
  have hi : ∀ i, blocks-(m+1)+(i+1) = blocks-m+i := by omega
  simp only [hi,Nat.add_mul,Nat.one_mul,pow_add]
  have he : blocks-(m+1) = blocks-1-m := by omega
  rw [he]
  congr 1
  · apply Finset.sum_congr rfl
    intro i hi
    ring

theorem rect_outer {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X)
    (coeff : Array Int) (powers : Array Ival) (block blocks : Nat)
    (hp : ∀ i, i ≤ block → x^i ∈ powers[i]!) :
    ∀ m ≤ blocks, rectPrefix coeff x block blocks m ∈
      (List.range m).foldl (fun acc b =>
        Ival.add p (Ival.mul p acc powers[block]!)
          ((List.range block).foldl (fun v j =>
            if (blocks-1-b)*block+j < coeff.size then
              Ival.add p v (Ival.mul p (Ival.pt (Dy.ofInt coeff[(blocks-1-b)*block+j]!)) powers[j]!)
            else v) Ival.zero)) Ival.zero := by
  intro m hm
  induction m with
  | zero => simpa [rectPrefix] using Ival.mem_zero
  | succ m ih =>
    rw [rectPrefix_step coeff x block blocks m (by omega),List.range_succ,List.foldl_append]
    exact Ival.mem_add (Ival.mem_mul (ih (by omega)) (hp block le_rfl))
      (rect_inner hx coeff powers block (blocks-1-m) hp block le_rfl)

theorem rectPrefix_total (coeff : Array Int) (x : ℝ) (block blocks : Nat)
    (hlen : coeff.size ≤ blocks*block) :
    rectPrefix coeff x block blocks blocks =
      ∑ i ∈ Finset.range coeff.size, (coeff[i]! : ℝ)*x^i := by
  have hblock : rectPrefix coeff x block blocks blocks =
      ∑ i ∈ Finset.range (blocks*block),
        if i < coeff.size then (coeff[i]! : ℝ)*x^i else 0 := by
    rw [sum_range_blocks]
    simp only [rectPrefix,Nat.sub_self,Nat.zero_add,rectBlock,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    split <;> simp_all [pow_add] <;> ring
  rw [hblock]
  calc
    _ = ∑ i ∈ Finset.range coeff.size,
        if i < coeff.size then (coeff[i]! : ℝ)*x^i else 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hlen)
      intro i hi hnot
      simp only [Finset.mem_range,not_lt] at hnot
      simp [not_lt.mpr hnot]
    _ = _ := Finset.sum_congr rfl (fun i hi => if_pos (Finset.mem_range.mp hi))

theorem rectEval_sound {p : Nat} {x : ℝ} {X : Ival} (hx : x ∈ X) (coeff : Array Int) :
    (∑ i ∈ Finset.range coeff.size, (coeff[i]! : ℝ)*x^i) ∈ rectEval p coeff X := by
  by_cases he : coeff.isEmpty = true
  · have hz : coeff.size = 0 := by simpa using he
    simpa [rectEval,he,hz] using Ival.mem_zero
  · let block := max 1 coeff.size.sqrt
    let blocks := (coeff.size+block-1)/block
    let powers := (List.range block).foldl
      (fun ps _ => ps.push (Ival.mul p ps.back! X)) #[Ival.one]
    have hpow : ∀ i, i ≤ block → x^i ∈ powers[i]! := (rect_powers hx block).2
    have hb : 0 < block := by dsimp [block]; omega
    have hsize : coeff.size ≤ blocks*block := by
      have hm := Nat.mod_lt (coeff.size+block-1) hb
      have hd := Nat.mod_add_div (coeff.size+block-1) block
      rw [Nat.mul_comm block ((coeff.size+block-1)/block)] at hd
      dsimp only [blocks]
      omega
    have hres := rect_outer (p := p) hx coeff powers block blocks hpow blocks le_rfl
    rw [rectPrefix_total coeff x block blocks hsize] at hres
    unfold rectEval
    simp only [he,↓reduceIte]
    simp only [Std.Legacy.Range.forIn_eq_forIn_range',forIn_ite_yield_eq_foldl,
      List.forIn_pure_yield_eq_foldl,bind]
    simpa [block,blocks,powers,Std.Legacy.Range.size,← List.range_eq_range',Id.run,pure,bind] using hres

end Lynth.Interval.Integral
