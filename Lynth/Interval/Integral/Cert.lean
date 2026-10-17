import Lynth.Interval.Integral.Panel

/-! Replayable quadrature partitions and final strict accuracy checks. -/

namespace Lynth.Interval.Integral

open Intgrl

inductive Method where
  | direct
  | gauss (table : Nat) (rho : Dy)
deriving Repr, Inhabited

structure Piece where
  a : Dy
  b : Dy
  method : Method
deriving Repr, Inhabited

structure Certificate where
  a : Dy
  b : Dy
  reverse : Bool := false
  tables : Array NodeTable := #[]
  pieces : List Piece
deriving Repr, Inhabited

def dyEq (a b : Dy) : Bool := a.toRat == b.toRat

def partitionCheck (cert : Certificate) : Bool :=
  match cert.pieces with
  | [] => false
  | p :: ps =>
    dyEq p.a cert.a &&
    dyEq (ps.getLastD p).b cert.b &&
    cert.pieces.all (fun p => Dy.leB p.a p.b) &&
    (cert.pieces.zip cert.pieces.tail).all (fun (p,q) => dyEq p.b q.a)

def pieceEncl (c : Ctx) (e : Term) (tables : Array NodeTable)
    (weights : Array (List Ival)) (p : Piece) : Option Ival :=
  match p.method with
  | .direct => if dyEq p.a p.b then some Ival.zero else directPanel c e p.a p.b
  | .gauss i ρ => do
    if !Dy.ltB p.a p.b then none else
      gaussPanel c e p.a p.b ρ (← tables[i]?) (← weights[i]?)

def hullPoint (I : Ival) (x : Dy) : Ival :=
  ⟨I.lo.map (Dy.min x), I.hi.map (Dy.max x)⟩

def endpointError (c : Ctx) (e : Term) (I : Ival) (anchor : Dy) : Option Dy :=
  match I.lo, I.hi with
  | some a, some b =>
    if dyEq a anchor && dyEq b anchor then some Dy.zero else
      let len := Ival.abs (Ival.sub c.prec I (Ival.pt anchor))
      let vals := Ival.abs (evalR c e (hullPoint I anchor))
      (Ival.mul c.prec len vals).hi
  | _, _ => none

def finiteEncl (c : Ctx) (e A B : Term) (kind : Region)
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
  sorry

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

def closeCheck (c : Ctx) (S : Ival) (q : ℚ) (tol : Term) : Bool :=
  Ival.ltB (Ival.abs (Ival.sub c.prec S (Ival.ofRat c.prec q))) (evalR c tol Ival.zero)

theorem closeCheck_sound {c : Ctx} (hc : c.Valid) {S : Ival} {v : ℝ}
    (hv : v ∈ S) {q : ℚ} {tol : Term} (h : closeCheck c S q tol = true) :
    |v - (q : ℝ)| < tol.real 0 :=
  Ival.lt_of_ltB (Ival.mem_abs (Ival.mem_sub hv (Ival.mem_ofRat _ _)))
    (evalR_sound hc tol Ival.mem_zero) h

def finiteCheck (c : Ctx) (e A B : Term) (kind : Region)
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
