import Lynth.Interval.Integral.Math.NestedDefs

/-! Measurability of binder-aware real expressions, including variable limits. -/
namespace Intgrl
open MeasureTheory

theorem measurable_param_setIntegral {α : Type*} [MeasurableSpace α]
    {F : α × ℝ → ℝ} (hF : Measurable F) {s : α → Set ℝ}
    (hs : MeasurableSet {p : α × ℝ | p.2 ∈ s p.1}) :
    Measurable (fun a => ∫ x in s a, F (a,x)) := by
  have hG := (hF.indicator hs).stronglyMeasurable.integral_prod_right' (ν := volume)
  convert hG.measurable using 1
  funext a
  have hsa : MeasurableSet (s a) := by
    simpa using hs.preimage (measurable_const.prodMk measurable_id)
  rw [← integral_indicator hsa]
  congr 1

theorem measurable_domainValue {α : Type*} [MeasurableSpace α]
    (k : NDomain) {F : α × ℝ → ℝ} (hF : Measurable F) {a b : α → ℝ}
    (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun p => k.value (fun x => F (p,x)) (a p) (b p)) := by
  have hlo : Measurable (fun p : α × ℝ => a p.1) := ha.comp measurable_fst
  have hhi : Measurable (fun p : α × ℝ => b p.1) := hb.comp measurable_fst
  have hcc := measurable_param_setIntegral hF (s := fun p => Set.Icc (a p) (b p))
    ((measurableSet_le hlo measurable_snd).inter (measurableSet_le measurable_snd hhi))
  have hoc := measurable_param_setIntegral hF (s := fun p => Set.Ioc (a p) (b p))
    ((measurableSet_lt hlo measurable_snd).inter (measurableSet_le measurable_snd hhi))
  have hco := measurable_param_setIntegral hF (s := fun p => Set.Ico (a p) (b p))
    ((measurableSet_le hlo measurable_snd).inter (measurableSet_lt measurable_snd hhi))
  have hoo := measurable_param_setIntegral hF (s := fun p => Set.Ioo (a p) (b p))
    ((measurableSet_lt hlo measurable_snd).inter (measurableSet_lt measurable_snd hhi))
  cases k with
  | interval =>
    have hrev := measurable_param_setIntegral hF (s := fun p => Set.Ioc (b p) (a p))
      ((measurableSet_lt hhi measurable_snd).inter (measurableSet_le measurable_snd hlo))
    exact hoc.sub hrev
  | icc => exact hcc
  | ioc => exact hoc
  | ico => exact hco
  | ioo => exact hoo
  | right => exact measurable_param_setIntegral hF (s := fun p => Set.Ioi (a p)) (measurableSet_lt hlo measurable_snd)
  | left => exact measurable_param_setIntegral hF (s := fun p => Set.Iio (a p)) (measurableSet_lt measurable_snd hlo)
  | whole => exact hF.stronglyMeasurable.integral_prod_right'.measurable

theorem NExpr.measurable_env (e : NExpr) :
    ∀ {α : Type} [MeasurableSpace α] (fs : List (α → ℝ)),
      (∀ f ∈ fs, Measurable f) → Measurable (fun x => e.real (fs.map (fun f => f x))) := by
  induction e with
  | var i =>
    intro α _ fs hfs
    cases hf : fs[i]? with
    | none => simpa [NExpr.real,List.getElem?_map,hf] using (measurable_const (a := (0:ℝ)))
    | some f =>
      simpa [NExpr.real,List.getElem?_map,hf] using hfs f (List.mem_of_getElem? hf)
  | rat q => intro α _ fs hfs; exact measurable_const
  | pi => intro α _ fs hfs; exact measurable_const
  | unary op e ih =>
    intro α _ fs hfs
    exact (Term.measurable (.unary op .var)).comp (ih fs hfs)
  | binary op e f ihe ihf =>
    intro α _ fs hfs
    have he := ihe fs hfs
    have hf := ihf fs hfs
    cases op with
    | add => exact he.add hf
    | sub => exact he.sub hf
    | mul => exact he.mul hf
    | div => exact he.div hf
    | max => exact he.max hf
    | min => exact he.min hf
  | pow e n ih => intro α _ fs hfs; exact (ih fs hfs).pow_const n
  | rpow e q ih =>
    intro α _ fs hfs
    have he := ih fs hfs
    exact (Term.measurable (.rpow .var q)).comp he
  | integral k a b f iha ihb ihf =>
    intro α _ fs hfs
    let gs : List (α × ℝ → ℝ) := fs.map (fun f p => f p.1) ++ [Prod.snd]
    have hgs : ∀ g ∈ gs, Measurable g := by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨f,hf,rfl⟩ := List.mem_map.mp hg
        exact (hfs f hf).comp measurable_fst
      · have he : g = Prod.snd := List.mem_singleton.mp hg
        subst g
        exact measurable_snd
    have hf : Measurable (fun p : α × ℝ =>
        f.real (fs.map (fun g => g p.1) ++ [p.2])) := by
      simpa [gs,List.map_map,Function.comp_def] using ihf gs hgs
    exact measurable_domainValue k hf (iha fs hfs) (ihb fs hfs)

theorem NExpr.measurable_body (e : NExpr) (xs : List ℝ) :
    Measurable (fun x => e.real (xs++[x])) := by
  have hm := e.measurable_env (xs.map (fun a (_ : ℝ) => a) ++ [id]) (by
    intro f hf
    rcases List.mem_append.mp hf with hf | hf
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hf
      exact measurable_const
    · have he : f = id := List.mem_singleton.mp hf
      subst f
      exact measurable_id)
  simpa [List.map_map,Function.comp_def] using hm

end Intgrl
