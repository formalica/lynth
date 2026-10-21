import Lynth.Interval.Integral.NestedPrimitiveProof
import Lynth.Interval.Integral.NestedFormulaProof
import Lynth.Interval.Integral.NestedCert
import Lynth.Interval.Integral.Bounds

/-! Real range and convergence lemmas for the recursive integral evaluator. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl Fns MeasureTheory

set_option maxHeartbeats 800000 in
-- The fuel induction checks every early return in the numerical evaluator.
theorem boundR_isFinite {fuel : Nat} {c : Ctx} {e : Expr} {env : Array Ival}
    {I : Ival} (h : boundR fuel c e env = some I) : I.isFinite = true := by
  induction fuel generalizing e env I with
  | zero => simp [boundR] at h
  | succ fuel ih =>
    cases e <;> simp only [boundR, bind, pure, Option.bind_eq_some_iff] at h
    all_goals repeat' (
      try simp only [Option.bind_eq_some_iff] at h
      first
      | (guard_hyp h : ∃ _, _; rcases h with ⟨_, _, h⟩)
      | exact ih h
      | (cases Option.some.inj h; assumption)
      | (clear ih; simp_all [Ival.isFinite, Ival.zero, Ival.pt]; done)
      | split at h)

    all_goals
      cases Option.some.inj h
      clear ih
      simp_all [Ival.isFinite, Ival.zero, Ival.pt]

theorem endpointHull_mem {A B : Ival} {a b x : ℝ} (ha : a ∈ A) (hb : b ∈ B)
    (hx : x ∈ Set.uIcc a b) :
    x ∈ (⟨A.lo.bind (fun u => B.lo.map (Dy.min u)),
      A.hi.bind (fun u => B.hi.map (Dy.max u))⟩ : Ival) := by
  constructor
  · intro l hl
    cases hal : A.lo with
    | none => simp [hal] at hl
    | some al =>
      cases hbl : B.lo with
      | none => simp [hal, hbl] at hl
      | some bl =>
        have he : Dy.min al bl = l := by simpa [hal, hbl] using hl
        rw [← he]
        exact (le_min
          ((Ival.min_toReal_le_left al bl).trans (ha.1 al hal))
          ((Ival.min_toReal_le_right al bl).trans (hb.1 bl hbl))).trans hx.1
  · intro u hu
    cases hau : A.hi with
    | none => simp [hau] at hu
    | some au =>
      cases hbu : B.hi with
      | none => simp [hau, hbu] at hu
      | some bu =>
        have he : Dy.max au bu = u := by simpa [hau, hbu] using hu
        rw [← he]
        exact hx.2.trans (max_le
          ((ha.2 au hau).trans (Ival.le_max_toReal_left au bu))
          ((hb.2 bu hbu).trans (Ival.le_max_toReal_right au bu)))

theorem hullZero_mem {V : Ival} {x : ℝ} (hx : x = 0 ∨ x ∈ V) :
    x ∈ (⟨V.lo.map (Dy.min Dy.zero), V.hi.map (Dy.max Dy.zero)⟩ : Ival) := by
  constructor
  · intro l hl
    cases hv : V.lo with
    | none => simp [hv] at hl
    | some v =>
      have he : Dy.min Dy.zero v = l := by simpa [hv] using hl
      rw [← he]
      rcases hx with rfl | hx
      · simpa [Dy.toReal_def] using Ival.min_toReal_le_left Dy.zero v
      · exact (Ival.min_toReal_le_right Dy.zero v).trans (hx.1 v hv)
  · intro u hu
    cases hv : V.hi with
    | none => simp [hv] at hu
    | some v =>
      have he : Dy.max Dy.zero v = u := by simpa [hv] using hu
      rw [← he]
      rcases hx with rfl | hx
      · simpa [Dy.toReal_def] using Ival.le_max_toReal_left Dy.zero v
      · exact (hx.2 v hv).trans (Ival.le_max_toReal_right Dy.zero v)

theorem finite_integral_zero_width {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} (ha : a.Converges xs) (hb : b.Converges xs)
    (hab : a.real xs = b.real xs) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = 0 := by
  have hi : IntervalIntegrable (fun x => f.real (xs ++ [x])) volume
      (a.real xs) (b.real xs) := by rw [hab]
  have hd := finite_domain_of_interval hk hab.le hi
  refine ⟨⟨ha, hb, hd.1, ?_⟩, ?_⟩
  · cases k <;> simp_all [NDomain.finite]
  · change k.value _ _ _ = 0
    rw [hd.2, hab, intervalIntegral.integral_same]

theorem finite_integral_empty {k : NDomain} (hk : k.finite = true)
    (hki : k ≠ .interval) {a b f : Expr} {xs : List ℝ}
    (ha : a.Converges xs) (hb : b.Converges xs) (hab : b.real xs ≤ a.real xs) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs = 0 := by
  rcases hab.eq_or_lt with he | he
  · exact finite_integral_zero_width hk ha hb he.symm
  have hcc : Set.Icc (a.real xs) (b.real xs) = ∅ := Set.Icc_eq_empty_of_lt he
  have hco : Set.Ico (a.real xs) (b.real xs) = ∅ := Set.Ico_eq_empty_of_le hab
  have hoc : Set.Ioc (a.real xs) (b.real xs) = ∅ := Set.Ioc_eq_empty_of_le hab
  have hoo : Set.Ioo (a.real xs) (b.real xs) = ∅ := Set.Ioo_eq_empty_of_le hab
  cases k <;> simp_all [NExpr.Converges, NExpr.real, NDomain.Converges,
    NDomain.value, NDomain.finite, integrableOn_empty]

theorem integral_mem_product_oriented {f : ℝ → ℝ} {a b : ℝ} {V L W : Ival}
    (hm : Measurable f) (hfinite : V.isFinite = true) (hL : b - a ∈ L)
    (hV : ∀ x ∈ Set.uIoo a b, f x ∈ V) (hVne : ∃ v : ℝ, v ∈ V)
    (hmul : ∀ l ∈ L, ∀ v ∈ V, l * v ∈ W) :
    IntervalIntegrable f volume a b ∧ (∫ x in a..b, f x) ∈ W := by
  rcases le_total a b with hab | hba
  · exact integral_mem_product hab hm hfinite hL
      (by simpa only [Set.uIoo_of_le hab] using hV) hVne hmul
  · have hneg : a - b ∈ Ival.neg L := by
      simpa only [neg_sub] using Ival.mem_neg hL
    have hi := integral_mem_product hba hm hfinite hneg
      (by simpa only [Set.uIoo_of_ge hba] using hV) hVne
      (W := Ival.neg W) (by
        intro l hl v hv
        have hl' : -l ∈ L := by
          simpa [Ival.mem_def, Ival.neg, Option.map_map, Function.comp_def,
            Vendor.Dyadic.neg] using Ival.mem_neg hl
        have hp := Ival.mem_neg (hmul (-l) hl' v hv)
        simpa only [neg_mul, neg_neg] using hp)
    refine ⟨hi.1.symm, ?_⟩
    have hh := Ival.mem_neg hi.2
    simpa [Ival.mem_def, Ival.neg, Option.map_map, Function.comp_def, Vendor.Dyadic.neg,
      ← intervalIntegral.integral_symm] using hh

theorem finite_integral_range {k : NDomain} (hk : k.finite = true)
    {a b f : Expr} {xs : List ℝ} {V L W : Ival}
    (ha : a.Converges xs) (hb : b.Converges xs)
    (horder : k ≠ .interval → a.real xs ≤ b.real xs)
    (hfinite : V.isFinite = true) (hL : b.real xs - a.real xs ∈ L)
    (hV : ∀ x ∈ Set.uIoo (a.real xs) (b.real xs),
      f.Converges (xs ++ [x]) ∧ f.real (xs ++ [x]) ∈ V)
    (hVne : ∃ v : ℝ, v ∈ V)
    (hmul : ∀ l ∈ L, ∀ v ∈ V, l * v ∈ W) :
    (NExpr.integral k a b f).Converges xs ∧
      (NExpr.integral k a b f).real xs ∈ W := by
  have hi := integral_mem_product_oriented (f.measurable_body xs) hfinite hL
    (fun x hx => (hV x hx).2) hVne hmul
  by_cases hki : k = .interval
  · subst k
    exact ⟨⟨ha, hb, hi.1, fun x hx => (hV x hx).1⟩, hi.2⟩
  · have hab := horder hki
    have hd := finite_domain_of_interval hk hab hi.1
    refine ⟨⟨ha, hb, hd.1, ?_⟩, ?_⟩
    · cases k <;> simp_all only [NDomain.finite, Bool.false_eq_true]
      all_goals exact fun x hx => (hV x (by simpa only [Set.uIoo_of_le hab] using hx)).1
    · change k.value _ _ _ ∈ W
      rw [hd.2]
      exact hi.2

theorem panel_chain_sound {F : ℝ → ℝ} {cert : Certificate}
    {eval : Piece → Option Ival} {vals : List Ival} {prec : Nat}
    (hp : partitionCheck cert = true)
    (heval : ∀ p ∈ cert.pieces, p.a.toReal ≤ p.b.toReal →
      ∀ I, eval p = some I →
        IntervalIntegrable F volume p.a.toReal p.b.toReal ∧
          (∫ x in p.a.toReal..p.b.toReal, F x) ∈ I)
    (hvals : cert.pieces.mapM eval = some vals) :
    IntervalIntegrable F volume cert.a.toReal cert.b.toReal ∧
      (∫ x in cert.a.toReal..cert.b.toReal, F x) ∈ balancedSum prec vals := by
  have hv := mapM_some_forall₂ hvals
  have horder : ∀ p ∈ cert.pieces, p.a.toReal ≤ p.b.toReal := by
    cases hps : cert.pieces with
    | nil => simp [partitionCheck, hps] at hp
    | cons p ps =>
      have hh := hp
      simp only [partitionCheck, hps, Bool.and_eq_true] at hh
      intro q hq
      exact Dy.toReal_le_of_leB ((List.all_eq_true.mp hh.1.2) q hq)
  have hgood : List.Forall₂ (fun p V =>
      IntervalIntegrable F volume p.a.toReal p.b.toReal ∧
        (∫ x in p.a.toReal..p.b.toReal, F x) ∈ V) cert.pieces vals := by
    apply List.forall₂_of_length_eq_of_get hv.length_eq
    intro i hi hj
    exact heval _ (List.getElem_mem hi) (horder _ (List.getElem_mem hi)) _
      (hv.get hi hj)
  obtain ⟨hints, hmems⟩ := (List.forall₂_and_left cert.pieces vals).mp hgood
  have hsum := balancedSum_mem (p := prec)
    (show List.Forall₂ (fun (x : ℝ) (I : Ival) => x ∈ I)
      (cert.pieces.map fun p => ∫ x in p.a.toReal..p.b.toReal, F x) vals by
        simpa only [List.forall₂_map_left_iff] using hmems)
  cases hps : cert.pieces with
  | nil => simp [partitionCheck, hps] at hp
  | cons p ps =>
    simp only [partitionCheck, hps, Bool.and_eq_true] at hp
    have ha : p.a.toReal = cert.a.toReal := by
      have he : p.a.toRat = cert.a.toRat := by simpa [dyEq] using hp.1.1.1
      exact congrArg (fun q : ℚ => (q : ℝ)) he
    have hb : (ps.getLastD p).b.toReal = cert.b.toReal := by
      have he : (ps.getLastD p).b.toRat = cert.b.toRat := by simpa [dyEq] using hp.1.1.2
      exact congrArg (fun q : ℚ => (q : ℝ)) he
    have hchain := piece_chain_integral p ps hp.2 (by simpa only [hps] using hints)
    refine ⟨by simpa only [ha, hb] using hchain.1, ?_⟩
    rw [hps] at hsum
    rw [← hchain.2, ha, hb] at hsum
    exact hsum

theorem uncertainEndpoint_sound_of_bound {c : Ctx} {e : Expr}
    {env : Array Ival} {xs : List ℝ} {I : Ival} {a err : Dy} {x : ℝ}
    (hx : x ∈ I)
    (hbound : ∀ V, boundR (e.size + 32) c e (env.push (hullPoint I a)) = some V →
      ∀ t ∈ hullPoint I a, e.Converges (xs ++ [t]) ∧ e.real (xs ++ [t]) ∈ V)
    (h : uncertainEndpoint c e env I a = some err) :
    IntervalIntegrable (fun t => e.real (xs ++ [t])) volume x a.toReal ∧
      |(∫ t in x..a.toReal, e.real (xs ++ [t]))| ≤ err.toReal ∧
      ∀ t ∈ Set.uIoo x a.toReal, e.Converges (xs ++ [t]) := by
  cases hlo : I.lo with
  | none => simp [uncertainEndpoint, hlo] at h
  | some lo =>
    cases hhi : I.hi with
    | none => simp [uncertainEndpoint, hlo, hhi] at h
    | some hi =>
      simp only [uncertainEndpoint, hlo, hhi, bind, Option.bind_some] at h
      split at h
      · rename_i he
        have hh : lo.toRat = a.toRat ∧ hi.toRat = a.toRat := by simpa [dyEq] using he
        have hxa : x = a.toReal := le_antisymm
          (by simpa [Dy.toReal_def, hh.2] using hx.2 hi hhi)
          (by simpa [Dy.toReal_def, hh.1] using hx.1 lo hlo)
        have herr : Dy.zero = err := Option.some.inj h
        subst err
        simp [hxa, Dy.toReal_def]
      · cases hv : boundR (e.size + 32) c e (env.push (hullPoint I a)) with
        | none => simp [hv] at h
        | some V =>
          simp only [hv, Option.bind_some] at h
          have hpoint := hbound V hv
          have hp : ∀ t ∈ Set.uIcc x a.toReal,
              |x - a.toReal| * |e.real (xs ++ [t])| ≤ err.toReal := by
            intro t ht
            exact (Ival.mem_mul (p := c.prec)
              (Ival.mem_abs (Ival.mem_sub (p := c.prec) hx (Ival.mem_pt a)))
              (Ival.mem_abs (hpoint t (hullPoint_mem hx ht)).2)).2 err h
          have herr : 0 ≤ err.toReal :=
            (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hp x Set.left_mem_uIcc)
          have hconv : ∀ t ∈ Set.uIoo x a.toReal, e.Converges (xs ++ [t]) := by
            intro t ht
            exact (hpoint t (hullPoint_mem hx ⟨ht.1.le, ht.2.le⟩)).1
          by_cases he : x = a.toReal
          · exact ⟨by simp [he], by simpa [he] using herr, hconv⟩
          · have hpos : 0 < |x - a.toReal| := abs_pos.mpr (sub_ne_zero.mpr he)
            let C := err.toReal / |x - a.toReal|
            have hnorm : ∀ t ∈ Set.uIcc x a.toReal, |e.real (xs ++ [t])| ≤ C := by
              intro t ht
              exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using hp t ht)
            have hint : IntervalIntegrable (fun t => e.real (xs ++ [t])) volume x a.toReal := by
              apply (intervalIntegrable_iff').mpr
              exact IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
                (e.measurable_body xs).aestronglyMeasurable.restrict C
                (ae_restrict_of_forall_mem measurableSet_uIcc
                  (fun t ht => by simpa only [Real.norm_eq_abs] using hnorm t ht))
            refine ⟨hint, ?_, hconv⟩
            have hn := intervalIntegral.norm_integral_le_of_norm_le_const
              (f := fun t => e.real (xs ++ [t])) (C := C) (fun t ht => by
                simpa only [Real.norm_eq_abs] using hnorm t (Set.uIoc_subset_uIcc ht))
            simpa only [Real.norm_eq_abs, abs_sub_comm a.toReal x, C,
              div_mul_cancel₀ _ (ne_of_gt hpos)] using hn

end Lynth.Interval.Integral.Nested
