module

public import Init.Control.Basic
public import Init.Core
public import Init.Data.Array.Basic
public import Init.Data.List.Basic
public import Init.Data.List.Control
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Option.Basic
public import Init.Data.Rat.Basic
public import Init.GetElem
public import Init.Prelude
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Integral.Eval
public import Lynth.Interval.Integral.Legendre
public import Lynth.Interval.Integral.Math.Integrand
public import Lynth.Interval.Integral.Panel
public import Lynth.Interval.Num.Dy
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Vendor.Dyadic
import all Lynth.Interval.Integral.Panel
import all Lynth.Interval.Integral.SyntaxEq

/-! Replayable quadrature partitions and final strict accuracy checks. -/

namespace Lynth.Interval.Integral

open Intgrl

public inductive Method where
  | direct
  | gauss (table : Nat) (rho : Dy)
deriving Repr, Inhabited

public structure Piece where
  a : Dy
  b : Dy
  method : Method
deriving Repr, Inhabited

public structure Certificate where
  a : Dy
  b : Dy
  reverse : Bool := false
  tables : Array NodeTable := #[]
  pieces : List Piece
deriving Repr, Inhabited

@[expose] public def dyEq (a b : Dy) : Bool := a.toRat == b.toRat

@[expose] public def partitionCheck (cert : Certificate) : Bool :=
  match cert.pieces with
  | [] => false
  | p :: ps =>
    dyEq p.a cert.a &&
    dyEq (ps.getLastD p).b cert.b &&
    cert.pieces.all (fun p => Dy.leB p.a p.b) &&
    (cert.pieces.zip cert.pieces.tail).all (fun (p,q) => dyEq p.b q.a)

@[expose] public def pieceEncl (c : Ctx) (e : Term) (tables : Array NodeTable)
    (weights : Array (List Ival)) (p : Piece) : Option Ival :=
  match p.method with
  | .direct => if dyEq p.a p.b then some Ival.zero else directPanel c e p.a p.b
  | .gauss i ρ => do
    if !Dy.ltB p.a p.b then none else
      gaussPanel c e p.a p.b ρ (← tables[i]?) (← weights[i]?)

@[expose] public def hullPoint (I : Ival) (x : Dy) : Ival :=
  ⟨I.lo.map (Dy.min x), I.hi.map (Dy.max x)⟩

@[expose] public def endpointError (c : Ctx) (e : Term) (I : Ival) (anchor : Dy) : Option Dy :=
  match I.lo, I.hi with
  | some a, some b =>
    if dyEq a anchor && dyEq b anchor then some Dy.zero else
      let len := Ival.abs (Ival.sub c.prec I (Ival.pt anchor))
      let vals := Ival.abs (evalR c e (hullPoint I anchor))
      (Ival.mul c.prec len vals).hi
  | _, _ => none

theorem hullPoint_mem {I : Ival} {x y : ℝ} {a : Dy} (hx : x ∈ I)
    (hy : y ∈ Set.uIcc x a.toReal) : y ∈ hullPoint I a := by
  constructor
  · intro lo hlo
    cases hl : I.lo with
    | none => simp [hullPoint, hl] at hlo
    | some l =>
      have he : Dy.min a l = lo := by simpa [hullPoint, hl] using hlo
      rw [← he]
      exact (le_min (Ival.min_toReal_le_right a l |>.trans (hx.1 l hl))
        (Ival.min_toReal_le_left a l)).trans hy.1
  · intro hi hhi
    cases hh : I.hi with
    | none => simp [hullPoint, hh] at hhi
    | some u =>
      have he : Dy.max a u = hi := by simpa [hullPoint, hh] using hhi
      rw [← he]
      exact hy.2.trans (max_le ((hx.2 u hh).trans (Ival.le_max_toReal_right a u))
        (Ival.le_max_toReal_left a u))

theorem endpointError_sound {c : Ctx} (hc : c.Valid) {e : Term} {I : Ival}
    {a err : Dy} {x : ℝ} (hx : x ∈ I) (h : endpointError c e I a = some err) :
    IntervalIntegrable e.real MeasureTheory.volume x a.toReal ∧
      |(∫ t in x..a.toReal, e.real t)| ≤ err.toReal := by
  cases hlo : I.lo with
  | none => simp [endpointError, hlo] at h
  | some lo =>
    cases hhi : I.hi with
    | none => simp [endpointError, hlo, hhi] at h
    | some hi =>
      simp only [endpointError, hlo, hhi] at h
      split at h
      · rename_i he
        have hh : lo.toRat = a.toRat ∧ hi.toRat = a.toRat := by simpa [dyEq] using he
        have hxa : x = a.toReal := le_antisymm
          (by simpa [Dy.toReal_def, hh.2] using hx.2 hi hhi)
          (by simpa [Dy.toReal_def, hh.1] using hx.1 lo hlo)
        have herr : Dy.zero = err := Option.some.inj h
        subst err
        simp [hxa, Dy.toReal_def]
      · have hp : ∀ t ∈ Set.uIcc x a.toReal,
            |x-a.toReal| * |e.real t| ≤ err.toReal := by
          intro t ht
          exact (Ival.mem_mul (p := c.prec)
            (Ival.mem_abs (Ival.mem_sub (p := c.prec) hx (Ival.mem_pt a)))
            (Ival.mem_abs (evalR_sound hc e (hullPoint_mem hx ht)))).2 err h
        have herr : 0 ≤ err.toReal :=
          (mul_nonneg (abs_nonneg _) (abs_nonneg _)).trans (hp x (Set.left_mem_uIcc))
        by_cases he : x = a.toReal
        · simpa [he] using herr
        · have hpos : 0 < |x-a.toReal| := abs_pos.mpr (sub_ne_zero.mpr he)
          let C := err.toReal / |x-a.toReal|
          have hbound : ∀ t ∈ Set.uIcc x a.toReal, |e.real t| ≤ C := by
            intro t ht
            exact (le_div_iff₀ hpos).mpr (by simpa [mul_comm] using hp t ht)
          have hint : IntervalIntegrable e.real MeasureTheory.volume x a.toReal := by
            apply (intervalIntegrable_iff').mpr
            exact MeasureTheory.IntegrableOn.of_bound isCompact_uIcc.measure_lt_top
              e.measurable.aestronglyMeasurable.restrict C
              (MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIcc
                (fun t ht => by simpa only [Real.norm_eq_abs] using hbound t ht))
          refine ⟨hint, ?_⟩
          have hn := intervalIntegral.norm_integral_le_of_norm_le_const (f := e.real)
            (C := C) (fun t ht => by
              simpa only [Real.norm_eq_abs] using hbound t (Set.uIoc_subset_uIcc ht))
          simpa only [Real.norm_eq_abs, abs_sub_comm a.toReal x, C,
            div_mul_cancel₀ _ (ne_of_gt hpos)] using hn

theorem piece_chain_integral {f : ℝ → ℝ} (p : Piece) (ps : List Piece)
    (hc : ((p::ps).zip ps).all (fun (a,b) => dyEq a.b b.a) = true)
    (hi : ∀ q ∈ p::ps,
      IntervalIntegrable f MeasureTheory.volume q.a.toReal q.b.toReal) :
    IntervalIntegrable f MeasureTheory.volume p.a.toReal (ps.getLastD p).b.toReal ∧
      (∫ x in p.a.toReal..(ps.getLastD p).b.toReal, f x) =
        ((p::ps).map fun q => ∫ x in q.a.toReal..q.b.toReal, f x).sum := by
  induction ps generalizing p with
  | nil => simpa using hi p (by simp)
  | cons q qs ih =>
    have hchecks : dyEq p.b q.a = true ∧
        ((q::qs).zip qs).all (fun (a,b) => dyEq a.b b.a) = true := by simpa using hc
    have heq : p.b.toReal = q.a.toReal := by
      have hrat : p.b.toRat = q.a.toRat := by simpa [dyEq] using hchecks.1
      exact congrArg (fun q : ℚ => (q : ℝ)) hrat
    have hp := hi p (by simp)
    have hq := ih q hchecks.2 (fun q hq => hi q (by simp [hq]))
    have htail : IntervalIntegrable f MeasureTheory.volume p.b.toReal (qs.getLastD q).b.toReal :=
      heq.symm ▸ hq.1
    refine ⟨by simpa only [List.getLastD_cons] using hp.trans htail, ?_⟩
    simpa only [List.getLastD_cons, heq, hq.2, List.map_cons, List.sum_cons] using
      (intervalIntegral.integral_add_adjacent_intervals hp htail).symm

@[expose] public def finiteEncl (c : Ctx) (e A B : Term) (kind : Region)
    (cert : Certificate) : Option Ival := do
  if !partitionCheck cert then none else do
    if !(cert.tables.all (fun t => t.check c)) then none else do
      let weights := cert.tables.map (fun t => t.weights c)
      let pieces ← cert.pieces.mapM (pieceEncl c e cert.tables weights)
      let core := balancedSum c.prec pieces
      let core := if cert.reverse then Ival.neg core else core
      let AI := evalR c A Ival.zero
      let BI := evalR c B Ival.zero
      if kind != .interval && !Ival.leB AI BI then none else do
        let a := if cert.reverse then cert.b else cert.a
        let b := if cert.reverse then cert.a else cert.b
        let ea ← endpointError c e AI a
        let eb ← endpointError c e BI b
        return Ival.widen c.prec core (Dy.addU c.prec ea eb)

theorem pieceEncl_sound {c : Ctx} (hc : c.Valid) {e : Term}
    {tables : Array NodeTable} (ht : tables.all (fun t => t.check c) = true)
    {p : Piece} (hab : p.a.toReal ≤ p.b.toReal) {I : Ival}
    (h : pieceEncl c e tables (tables.map (fun t => t.weights c)) p = some I) :
    IntervalIntegrable e.real MeasureTheory.volume p.a.toReal p.b.toReal ∧
      (∫ x in p.a.toReal..p.b.toReal, e.real x) ∈ I := by
  cases hm : p.method with
  | direct =>
    simp only [pieceEncl, hm] at h
    split at h
    · rename_i hz
      have heq : p.a.toReal = p.b.toReal := by
        have hr : p.a.toRat = p.b.toRat := by simpa [dyEq] using hz
        exact congrArg (fun q : ℚ => (q : ℝ)) hr
      have hI : Ival.zero = I := Option.some.inj h
      subst I
      simpa [heq] using (show (0 : ℝ) ∈ Ival.zero from Ival.mem_zero)
    · exact directPanel_sound hc hab h
  | gauss i ρ =>
    simp only [pieceEncl, hm] at h
    split at h
    · simp at h
    · rename_i hlt
      have hab' : p.a.toReal < p.b.toReal := Dy.toReal_lt_of_ltB (by simpa using hlt)
      cases hti : tables[i]? with
      | none => simp [hti] at h
      | some t =>
        have hcheck := (Array.all_eq_true_iff_forall_mem.mp ht) t
          (Array.mem_of_getElem? hti)
        have hw : (tables.map (fun t => t.weights c))[i]? = some (t.weights c) := by
          simp [hti]
        exact gaussPanel_sound hc hab' hcheck (by simpa [hti, hw] using h)

/-- Remaining interval adapter: joins checked panels, accounts for uncertain
endpoints and orientation, and changes finite interval endpoint conventions.
It consumes the individual panel proofs, so replay retains the GL error theorem. -/
theorem finiteAssembly_sound {c : Ctx} (hc : c.Valid) {e A B : Term}
    {kind : Region} (hkind : kind = .interval ∨ kind = .icc ∨ kind = .ioc ∨
      kind = .ico ∨ kind = .ioo)
    {cert : Certificate} {S : Ival}
    (hpieces : ∀ p ∈ cert.pieces, p.a.toReal ≤ p.b.toReal →
      ∀ I, pieceEncl c e cert.tables (cert.tables.map (fun t => t.weights c)) p = some I →
        IntervalIntegrable e.real MeasureTheory.volume p.a.toReal p.b.toReal ∧
          (∫ x in p.a.toReal..p.b.toReal, e.real x) ∈ I)
    (h : finiteEncl c e A B kind cert = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S := by
  unfold finiteEncl at h
  split at h
  · simp at h
  · rename_i hpartition
    have hpartition' : partitionCheck cert = true := by simpa using hpartition
    split at h
    · simp at h
    · dsimp only at h
      cases hv : cert.pieces.mapM
          (pieceEncl c e cert.tables (cert.tables.map (fun t => t.weights c))) with
      | none => simp [hv] at h
      | some vals =>
        simp only [hv, bind, Option.bind] at h
        have hvals := mapM_some_forall₂ hv
        have horder : ∀ p ∈ cert.pieces, p.a.toReal ≤ p.b.toReal := by
          cases hp : cert.pieces with
          | nil => simp [partitionCheck,hp] at hpartition'
          | cons p ps =>
            have hh := hpartition'
            simp only [partitionCheck,hp,Bool.and_eq_true] at hh
            intro q hq
            exact Dy.toReal_le_of_leB ((List.all_eq_true.mp hh.1.2) q hq)
        have hgood : List.Forall₂ (fun p V =>
            IntervalIntegrable e.real MeasureTheory.volume p.a.toReal p.b.toReal ∧
            (∫ x in p.a.toReal..p.b.toReal, e.real x) ∈ V) cert.pieces vals := by
          apply List.forall₂_of_length_eq_of_get hvals.length_eq
          intro i hi hj
          exact hpieces _ (List.getElem_mem hi) (horder _ (List.getElem_mem hi)) _
            (hvals.get hi hj)
        obtain ⟨hints, hmems⟩ := (List.forall₂_and_left cert.pieces vals).mp hgood
        have hsum := balancedSum_mem (p := c.prec)
          (show List.Forall₂ (fun (x : ℝ) (I : Ival) => x ∈ I)
            (cert.pieces.map fun p => ∫ x in p.a.toReal..p.b.toReal, e.real x) vals by
              simpa only [List.forall₂_map_left_iff] using hmems)
        have hcore : IntervalIntegrable e.real MeasureTheory.volume cert.a.toReal cert.b.toReal ∧
            (∫ x in cert.a.toReal..cert.b.toReal, e.real x) ∈ balancedSum c.prec vals := by
          cases hp : cert.pieces with
          | nil => simp [partitionCheck,hp] at hpartition'
          | cons p ps =>
            have hh := hpartition'
            simp only [partitionCheck,hp,Bool.and_eq_true] at hh
            have ha : p.a.toReal = cert.a.toReal := by
              have he : p.a.toRat = cert.a.toRat := by simpa [dyEq] using hh.1.1.1
              exact congrArg (fun q : ℚ => (q : ℝ)) he
            have hb : (ps.getLastD p).b.toReal = cert.b.toReal := by
              have he : (ps.getLastD p).b.toRat = cert.b.toRat := by simpa [dyEq] using hh.1.1.2
              exact congrArg (fun q : ℚ => (q : ℝ)) he
            have hchain := piece_chain_integral p ps hh.2 (by simpa only [hp] using hints)
            refine ⟨by simpa only [ha,hb] using hchain.1, ?_⟩
            rw [hp] at hsum
            rw [← hchain.2,ha,hb] at hsum
            exact hsum
        split at h
        · simp at h
        · rename_i hordered
          let a₀ := if cert.reverse then cert.b else cert.a
          let b₀ := if cert.reverse then cert.a else cert.b
          have horiented : IntervalIntegrable e.real MeasureTheory.volume a₀.toReal b₀.toReal ∧
              (∫ x in a₀.toReal..b₀.toReal, e.real x) ∈
                (if cert.reverse then Ival.neg (balancedSum c.prec vals) else balancedSum c.prec vals) := by
            cases hr : cert.reverse with
            | false => simpa only [a₀,b₀,hr,Bool.false_eq_true,↓reduceIte] using hcore
            | true =>
              refine ⟨by simpa only [a₀,b₀,hr,↓reduceIte] using hcore.1.symm, ?_⟩
              simp only [a₀,b₀,hr,↓reduceIte]
              rw [intervalIntegral.integral_symm]
              exact Ival.mem_neg hcore.2
          change ((endpointError c e (evalR c A Ival.zero) a₀).bind fun ea =>
            (endpointError c e (evalR c B Ival.zero) b₀).bind fun eb =>
              some (Ival.widen c.prec
                (if cert.reverse then Ival.neg (balancedSum c.prec vals) else balancedSum c.prec vals)
                (Dy.addU c.prec ea eb))) = some S at h
          cases hea : endpointError c e (evalR c A Ival.zero) a₀ with
          | none => simp [hea] at h
          | some ea =>
            cases heb : endpointError c e (evalR c B Ival.zero) b₀ with
            | none => simp [hea,heb] at h
            | some eb =>
              have hS : Ival.widen c.prec
                  (if cert.reverse then Ival.neg (balancedSum c.prec vals) else balancedSum c.prec vals)
                  (Dy.addU c.prec ea eb) = S := by
                simpa only [hea,heb,Option.bind_some,Option.some.injEq] using h
              have ha := endpointError_sound hc (evalR_sound hc A Ival.mem_zero) hea
              have hb := endpointError_sound hc (evalR_sound hc B Ival.mem_zero) heb
              have hi := ha.1.trans (horiented.1.trans hb.1.symm)
              have hdiff : (∫ x in A.real 0..B.real 0, e.real x) -
                  (∫ x in a₀.toReal..b₀.toReal, e.real x) =
                  (∫ x in A.real 0..a₀.toReal, e.real x) -
                    (∫ x in B.real 0..b₀.toReal, e.real x) := by
                rw [← intervalIntegral.integral_add_adjacent_intervals ha.1 (horiented.1.trans hb.1.symm),
                  ← intervalIntegral.integral_add_adjacent_intervals horiented.1 hb.1.symm,
                  intervalIntegral.integral_symm b₀.toReal (B.real 0)]
                ring
              have hbound : |(∫ x in A.real 0..B.real 0, e.real x) -
                  (∫ x in a₀.toReal..b₀.toReal, e.real x)| ≤ (Dy.addU c.prec ea eb).toReal := by
                rw [hdiff]
                apply ((abs_sub _ _).trans (add_le_add ha.2 hb.2)).trans
                change (ea.toRat : ℝ) + (eb.toRat : ℝ) ≤ ((Dy.addU c.prec ea eb).toRat : ℝ)
                exact_mod_cast Dy.le_addU c.prec ea eb
              have hm : (∫ x in A.real 0..B.real 0, e.real x) ∈ S := by
                rw [← hS]
                exact Ival.mem_widen horiented.2 hbound
              have hle : kind ≠ .interval → A.real 0 ≤ B.real 0 := by
                intro hk
                have hcheck : Ival.leB (evalR c A Ival.zero) (evalR c B Ival.zero) = true := by
                  simpa [hk] using hordered
                exact Ival.le_of_leB (evalR_sound hc A Ival.mem_zero)
                  (evalR_sound hc B Ival.mem_zero) hcheck
              rcases hkind with rfl | rfl | rfl | rfl | rfl
              · exact ⟨hi,hm⟩
              · have hab := hle (by intro he; cases he)
                exact ⟨(intervalIntegrable_iff_integrableOn_Icc_of_le hab).mp hi,
                  by simpa only [Region.value,Region.set,intervalIntegral.integral_of_le hab,
                    MeasureTheory.integral_Icc_eq_integral_Ioc] using hm⟩
              · have hab := hle (by intro he; cases he)
                exact ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp hi,
                  by simpa only [Region.value,Region.set,intervalIntegral.integral_of_le hab] using hm⟩
              · have hab := hle (by intro he; cases he)
                exact ⟨(intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp hi,
                  by simpa only [Region.value,Region.set,intervalIntegral.integral_of_le hab,
                    MeasureTheory.integral_Ico_eq_integral_Ioc] using hm⟩
              · have hab := hle (by intro he; cases he)
                exact ⟨(intervalIntegrable_iff_integrableOn_Ioo_of_le hab).mp hi,
                  by simpa only [Region.value,Region.set,intervalIntegral.integral_of_le hab,
                    MeasureTheory.integral_Ioc_eq_integral_Ioo] using hm⟩

theorem finiteEncl_sound {c : Ctx} (hc : c.Valid) {e A B : Term}
    {kind : Region} (hkind : kind = .interval ∨ kind = .icc ∨ kind = .ioc ∨
      kind = .ico ∨ kind = .ioo)
    {cert : Certificate} {S : Ival}
    (h : finiteEncl c e A B kind cert = some S) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      kind.value e.real (A.real 0) (B.real 0) ∈ S := by
  have ht : cert.tables.all (fun t => t.check c) = true := by
    by_contra hn
    have hn' : cert.tables.all (fun t => t.check c) = false := Bool.eq_false_iff.mpr hn
    unfold finiteEncl at h
    rw [hn'] at h
    simp at h
  exact finiteAssembly_sound hc hkind
    (fun _ _ hab _ hp => pieceEncl_sound hc ht hab hp) h

@[expose] public def closeCheck (c : Ctx) (S : Ival) (q : ℚ) (tol : Term) : Bool :=
  Ival.ltB (Ival.abs (Ival.sub c.prec S (Ival.ofRat c.prec q))) (evalR c tol Ival.zero)

theorem closeCheck_sound {c : Ctx} (hc : c.Valid) {S : Ival} {v : ℝ}
    (hv : v ∈ S) {q : ℚ} {tol : Term} (h : closeCheck c S q tol = true) :
    |v - (q : ℝ)| < tol.real 0 :=
  Ival.lt_of_ltB (Ival.mem_abs (Ival.mem_sub hv (Ival.mem_ofRat _ _)))
    (evalR_sound hc tol Ival.mem_zero) h

@[expose] public def finiteCheck (c : Ctx) (e A B : Term) (kind : Region)
    (cert : Certificate) (q : ℚ) (tol : Term) : Bool :=
  match kind with
  | .interval | .icc | .ioc | .ico | .ioo =>
    match finiteEncl c e A B kind cert with
    | some S => closeCheck c S q tol
    | none => false
  | _ => false

theorem finiteCheck_sound {c : Ctx} (hc : c.Valid) {e A B : Term}
    {kind : Region} {cert : Certificate} {q : ℚ} {tol : Term}
    (h : finiteCheck c e A B kind cert q tol = true) :
    kind.Converges e.real (A.real 0) (B.real 0) ∧
      |kind.value e.real (A.real 0) (B.real 0) - (q : ℝ)| < tol.real 0 := by
  have hk : kind = .interval ∨ kind = .icc ∨ kind = .ioc ∨ kind = .ico ∨ kind = .ioo := by
    cases kind <;> simp_all [finiteCheck]
  cases hs : finiteEncl c e A B kind cert with
  | none =>
    cases kind <;> simp_all [finiteCheck]
  | some S =>
    have hh := finiteEncl_sound hc hk hs
    refine ⟨hh.1, closeCheck_sound hc hh.2 ?_⟩
    cases kind <;> simp_all [finiteCheck]

theorem result_of_check {f : ℝ → ℝ} {a b tol : ℝ}
    {e A B T : Term} {c : Ctx} {kind : Region} {cert : Certificate} {q : ℚ}
    (hc : c.Valid) (hf : ∀ x, f x = e.real x)
    (ha : a = A.real 0) (hb : b = B.real 0) (htol : tol = T.real 0)
    (h : finiteCheck c e A B kind cert q T = true) :
    kind.Converges f a b ∧ |kind.value f a b - (q : ℝ)| < tol := by
  obtain rfl : f = e.real := funext hf
  subst a; subst b; subst tol
  exact finiteCheck_sound hc h

end Lynth.Interval.Integral
