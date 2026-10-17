import Lynth.Interval.Integral.Legendre
import Lynth.Interval.Integral.Math.GaussError
import Lynth.Interval.Integral.Math.IntegralBounds
import Lynth.Interval.Integral.Math.Legendre
import Lynth.Interval.Integral.Bounds

/-! Certified direct and analytic Gauss-Legendre panels. -/

namespace Lynth.Interval.Integral

open Intgrl Fns

def specialize (c : Ctx) (X : Ival) : Term → Option Term
  | .unary .floor .var =>
    match X.lo, X.hi with
    | some a, some b =>
      let k := Dy.floor a
      if Dy.leB b (Dy.ofInt (k+1)) then some (.rat k) else none
    | _, _ => none
  | .unary op a => do
    let A ← specialize c X a
    let V := evalR c A X
    match op with
    | .abs => if V.nonneg then some A else if V.nonpos then some (.unary .neg A) else none
    | .floor =>
      match (intFloorIval V).lo, (intFloorIval V).hi with
      | some a, some b => if a.toRat == b.toRat then some (.rat a.toRat) else none
      | _, _ => none
    | .log => if V.negv then some (.unary .log (.unary .neg A)) else some (.unary .log A)
    | .sqrt => if V.nonpos then some (.rat 0) else some (.unary .sqrt A)
    | _ => some (.unary op A)
  | .binary op a b => do
    let A ← specialize c X a
    let B ← specialize c X b
    let VA := evalR c A X
    let VB := evalR c B X
    match op with
    | .max =>
      if Ival.leB VA VB then some B else if Ival.leB VB VA then some A else none
    | .min =>
      if Ival.leB VA VB then some A else if Ival.leB VB VA then some B else none
    | _ => some (.binary op A B)
  | .pow a n => do return .pow (← specialize c X a) n
  | .rpow a q => do return .rpow (← specialize c X a) q
  | e => some e

theorem specialize_sound {c : Ctx} (hc : c.Valid) {X : Ival} {e a : Term}
    (h : specialize c X e = some a) {x : ℝ} (hx : x ∈ X)
    (hinterior : ∀ lo hi, X.lo = some lo → X.hi = some hi →
      lo.toReal < x ∧ x < hi.toReal) :
    a.real x = e.real x := by
  sorry

theorem pointPair_sound {c : Ctx} (hc : c.Valid) (n : ℕ) {x : Dy}
    (hx : |x.toReal| < 1) :
    (legendre n).eval x.toReal ∈ (pointPair c n x).1 ∧
      (legendre n).derivative.eval x.toReal ∈ (pointPair c n x).2 := by
  sorry

theorem onInterval_sound {c : Ctx} (hc : c.Valid) (n : ℕ) {X : Ival}
    {x : ℝ} (hx : x ∈ X)
    (hX : ∀ y : ℝ, y ∈ X → |y| < 1) :
    (legendre n).eval x ∈ (onInterval c n X).1 ∧
      (legendre n).derivative.eval x ∈ (onInterval c n X).2 := by
  sorry

/-- Table certification exposes only exact mathematical nodes and weights.
The remaining numeric bridge proofs stay here because they depend on Ival. -/
theorem NodeTable.sound {c : Ctx} (hc : c.Valid) (t : NodeTable)
    (h : t.check c = true) :
    ∃ x : Fin t.roots.length → ℝ,
      IsGaussNodes x ∧
      ∀ i, x i ∈ rootIval (t.roots[i]) ∧
        gaussWeight t.roots.length (x i) ∈ (t.weights c).getD i.val Ival.top := by
  sorry

def balancedSum (p : Nat) (xs : List Ival) : Ival :=
  let rec go : Nat → List Ival → Ival
    | 0, xs => xs.foldl (Ival.add p) Ival.zero
    | fuel + 1, xs =>
      if xs.length ≤ 4 then xs.foldl (Ival.add p) Ival.zero else
        let (a,b) := xs.splitAt (xs.length / 2)
        Ival.add p (go fuel a) (go fuel b)
  go 64 xs

def panelBox (a b : Dy) : Ival := ⟨some a, some b⟩

def directPanel (c : Ctx) (e : Term) (a b : Dy) : Option Ival :=
  let ext := (specialize c (panelBox a b) e).getD e
  let V := evalR c ext (panelBox a b)
  if V.isFinite then
    some (Ival.mul c.prec (Ival.ofRat c.prec (b.toRat - a.toRat)) V)
  else none

def ellipseBox (c : Ctx) (a b ρ : Dy) : CBox :=
  let p := c.prec
  let r := ρ.toRat
  let x := (r + 1/r) / 2
  let y := (r - 1/r) / 2
  let mid := Ival.ofRat p ((a.toRat + b.toRat) / 2)
  let delta := Ival.ofRat p ((b.toRat - a.toRat) / 2)
  CBox.add p (CBox.ofReal mid)
    (CBox.mul p (CBox.ofReal delta)
      ⟨Ival.ofRats p (-x) x, Ival.ofRats p (-y) y⟩)

def errorBound (c : Ctx) (n : Nat) (a b ρ : Dy) (M : Dy) : Option Dy :=
  let p := c.prec
  let r := Ival.pt ρ
  let num := Ival.mul p (Ival.ofRat p 64)
    (Ival.mul p (Ival.ofRat p ((b.toRat - a.toRat)/2)) (Ival.pt M))
  let den := Ival.mul p (Ival.ofRat p 15)
    (Ival.mul p (Ival.sub p r Ival.one) (Ival.npow p r (2*n-1)))
  (Ival.div p num den).hi

/-- Analytic test and remainder do not evaluate any quadrature nodes. -/
def analyticBound (c : Ctx) (e : Term) (a b ρ : Dy) : Option Dy := do
  if !(Dy.ltB Dy.one ρ) then none else do
    let ext ← specialize c (panelBox a b) e
    let Z := ellipseBox c a b ρ
    if !regularCheck c ext Z then none else
      (CBox.norm c.prec (evalC c ext Z)).hi

def gaussSamples (c : Ctx) (e : Term) (a b : Dy)
    (t : NodeTable) (weights : List Ival) : Ival :=
  let p := c.prec
  let mid := Ival.ofRat p ((a.toRat+b.toRat)/2)
  let delta := Ival.ofRat p ((b.toRat-a.toRat)/2)
  let vals := (t.roots.zip weights).map fun (r,w) =>
    mulSigned p w (evalR c e (Ival.add p mid (Ival.mul p delta (rootIval r))))
  mulSigned p delta (balancedSum p vals)

def gaussPanel (c : Ctx) (e : Term) (a b ρ : Dy)
    (t : NodeTable) (weights : List Ival) : Option Ival := do
  let M ← analyticBound c e a b ρ
  let err ← errorBound c t.roots.length a b ρ M
  return Ival.widen c.prec (gaussSamples c e a b t weights) err

theorem directPanel_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b : Dy}
    (hab : a.toReal ≤ b.toReal) {I : Ival}
    (h : directPanel c e a b = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  let ext := (specialize c (panelBox a b) e).getD e
  let V := evalR c ext (panelBox a b)
  change (if V.isFinite then
    some (Ival.mul c.prec (Ival.ofRat c.prec (b.toRat-a.toRat)) V)
    else none) = some I at h
  split at h
  · rename_i hfinite
    have hL : b.toReal - a.toReal ∈ Ival.ofRat c.prec (b.toRat-a.toRat) := by
      simpa only [Dy.toReal_def, Rat.cast_sub] using
        Ival.mem_ofRat c.prec (b.toRat-a.toRat)
    have hxbox : ∀ x ∈ Set.Icc a.toReal b.toReal, x ∈ panelBox a b := by
      intro x hx
      simpa only [panelBox, Ival.mem_mk, Ival.loLe_some, Ival.leHi_some] using
        (show a.toReal ≤ x ∧ x ≤ b.toReal from hx)
    have hext : ∀ x ∈ Set.Ioo a.toReal b.toReal, ext.real x = e.real x := by
      intro x hx
      cases hs : specialize c (panelBox a b) e with
      | none => simp [ext, hs]
      | some f =>
        dsimp only [ext]
        rw [hs]
        change f.real x = e.real x
        apply specialize_sound hc hs (hxbox x ⟨hx.1.le, hx.2.le⟩)
        intro lo hi hlo hhi
        have ha : lo = a := Option.some.inj hlo.symm
        have hb : hi = b := Option.some.inj hhi.symm
        simpa [ha, hb] using hx
    have hv : ∀ x ∈ Set.Ioo a.toReal b.toReal, e.real x ∈ V := by
      intro x hx
      rw [← hext x hx]
      exact evalR_sound hc ext (hxbox x ⟨hx.1.le, hx.2.le⟩)
    have hne : ∃ v : ℝ, v ∈ V :=
      ⟨ext.real a.toReal, evalR_sound hc ext (hxbox _ ⟨le_rfl,hab⟩)⟩
    have hh := integral_mem_mul (p := c.prec) hab e.measurable hfinite hL hv hne
    exact Option.some.inj h ▸ hh
  · simp at h

theorem NodeTable.positive {c : Ctx} {t : NodeTable}
    (h : t.check c = true) : 0 < t.roots.length := by
  cases hn : t.roots.length with
  | zero => simp [NodeTable.check, hn] at h
  | succ n => omega

/-- Geometric transport and branch selection for the complex bound. -/
theorem analyticBound_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b ρ M : Dy}
    (hab : a.toReal < b.toReal)
    (h : analyticBound c e a b ρ = some M) :
    1 < ρ.toReal ∧ 0 ≤ M.toReal ∧
      ∃ F : ℂ → ℂ,
        AnalyticOnNhd ℂ F ((affine a.toReal b.toReal) '' ellipse ρ.toReal) ∧
        (∀ z ∈ ellipse ρ.toReal, ‖F (affine a.toReal b.toReal z)‖ ≤ M.toReal) ∧
        (∀ x ∈ Set.Ioo a.toReal b.toReal, F x = (e.real x : ℂ)) := by
  sorry

theorem gaussSamples_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b : Dy}
    {t : NodeTable} {x : Fin t.roots.length → ℝ}
    (ht : t.check c = true)
    (hx : ∀ i, x i ∈ rootIval (t.roots[i]) ∧
      gaussWeight t.roots.length (x i) ∈ (t.weights c).getD i.val Ival.top) :
    ((b.toReal - a.toReal) / 2) *
      gaussSum x (fun z => e.real ((a.toReal + b.toReal) / 2 +
        (b.toReal - a.toReal) / 2 * z)) ∈
      gaussSamples c e a b t (t.weights c) := by
  sorry

theorem errorBound_sound {c : Ctx} {n : ℕ} {a b ρ M err : Dy}
    (hn : 0 < n) (hab : a.toReal < b.toReal)
    (hρ : 1 < ρ.toReal) (hM : 0 ≤ M.toReal)
    (h : errorBound c n a b ρ M = some err) :
    glError n ρ.toReal (((b.toReal - a.toReal) / 2) * M.toReal) ≤ err.toReal := by
  sorry

theorem gaussPanel_sound {c : Ctx} (hc : c.Valid) {e : Term} {a b ρ : Dy}
    (hab : a.toReal < b.toReal) {t : NodeTable} (ht : t.check c = true)
    {I : Ival} (h : gaussPanel c e a b ρ t (t.weights c) = some I) :
    IntervalIntegrable e.real MeasureTheory.volume a.toReal b.toReal ∧
      (∫ x in a.toReal..b.toReal, e.real x) ∈ I := by
  unfold gaussPanel at h
  cases hM : analyticBound c e a b ρ with
  | none => simp [hM] at h
  | some M =>
    rw [hM] at h
    cases herr : errorBound c t.roots.length a b ρ M with
    | none => simp [hM, herr] at h
    | some err =>
      change (errorBound c t.roots.length a b ρ M).bind
        (fun err => some (Ival.widen c.prec (gaussSamples c e a b t (t.weights c)) err)) =
          some I at h
      rw [herr] at h
      have heq : Ival.widen c.prec (gaussSamples c e a b t (t.weights c)) err = I :=
        Option.some.inj h
      subst I
      obtain ⟨hρ, hM0, F, hF, hbound, hagree⟩ := analyticBound_sound hc hab hM
      obtain ⟨x, hx, hmem⟩ := t.sound hc ht
      have hn := NodeTable.positive ht
      have hgl := gauss_error_real_affine hn hx hab hρ hM0 hF hbound hagree
      exact ⟨hgl.1, Ival.mem_widen (gaussSamples_sound hc ht hmem)
        (hgl.2.trans (errorBound_sound hn hab hρ hM0 herr))⟩

end Lynth.Interval.Integral
