import Lynth.Interval.Integral.Math.Integrand
import Lynth.Interval.Integral.Powers
import Lynth.Interval.Integral.Trig
import Lynth.Interval.Fns.Floor

namespace Lynth.Interval.Integral

open Intgrl Fns

/-- Normalize signs before multiplying. The existing nonnegative kernel needs
two endpoint products; the finite four-corner fallback needs eight. -/
def mulSigned (p : Nat) (X Y : Ival) : Ival :=
  if X.nonpos then
    if Y.nonpos then Ival.mul p (Ival.neg X) (Ival.neg Y)
    else Ival.neg (Ival.mul p (Ival.neg X) Y)
  else if Y.nonpos then Ival.neg (Ival.mul p X (Ival.neg Y))
  else Ival.mul p X Y

theorem mem_mulSigned {p : Nat} {x y : ℝ} {X Y : Ival}
    (hx : x ∈ X) (hy : y ∈ Y) : x * y ∈ mulSigned p X Y := by
  unfold mulSigned
  split
  · split
    · simpa using Ival.mem_mul (p := p) (Ival.mem_neg hx) (Ival.mem_neg hy)
    · simpa using Ival.mem_neg (Ival.mem_mul (p := p) (Ival.mem_neg hx) hy)
  · split
    · simpa using Ival.mem_neg (Ival.mem_mul (p := p) hx (Ival.mem_neg hy))
    · exact Ival.mem_mul hx hy

def Unary.evalR (c : Ctx) (op : Unary) (X : Ival) : Ival :=
  match op with
  | .neg => Ival.neg X | .inv => Ival.inv c.prec X
  | .exp => fastExpIval c X | .sin => fastSinIval c X | .cos => fastCosIval c X
  | .sinh => fastSinhIval c X | .cosh => (fastCoshIval c X).clampLo Dy.one
  | .log => logIval c X | .sqrt => Ival.sqrt c.prec X
  | .abs => Ival.abs X | .floor => intFloorIval X | .atan => atanIval c X

def Binary.evalR (c : Ctx) (op : Binary) (X Y : Ival) : Ival :=
  match op with
  | .add => Ival.add c.prec X Y | .sub => Ival.sub c.prec X Y
  | .mul => mulSigned c.prec X Y | .div => Ival.div c.prec X Y
  | .max => Ival.max X Y | .min => Ival.min X Y

/-- Shared evaluation and the exact unit-range bound for a fractional part. -/
def fractionalIval (c : Ctx) (X : Ival) : Ival :=
  ((Ival.sub c.prec X (intFloorIval X)).clampLo Dy.zero).clampHi Dy.one

theorem mem_fractionalIval {c : Ctx} {x : ℝ} {X : Ival} (hx : x ∈ X) :
    x - (⌊x⌋ : ℤ) ∈ fractionalIval c X := by
  apply Ival.mem_clampHi
  · apply Ival.mem_clampLo (Ival.mem_sub hx (mem_intFloor hx))
    simpa only [Dy.toReal_def, Dy.toRat_zero, Rat.cast_zero, Int.fract] using Int.fract_nonneg x
  · simpa only [Dy.toReal_def, Dy.toRat_one, Rat.cast_one, Int.fract] using (Int.fract_lt_one x).le

def evalR (c : Ctx) (e : Term) (X : Ival) : Ival :=
  match e with
  | .var => X | .rat q => Ival.ofRat c.prec q | .pi => c.pi
  | .unary op a => Unary.evalR c op (evalR c a X)
  | .binary op a b =>
    if op = .sub ∧ b = .unary .floor a then fractionalIval c (evalR c a X)
    else Binary.evalR c op (evalR c a X) (evalR c b X)
  | .pow a n => naturalPowerR c.prec (evalR c a X) n
  | .rpow a q => rationalPowerR c (evalR c a X) q

theorem unary_evalR_sound {c : Ctx} (hc : c.Valid) (op : Unary)
    {x : ℝ} {X : Ival} (hx : x ∈ X) :
    op.real x ∈ Unary.evalR c op X := by
  cases op with
  | neg => exact Ival.mem_neg hx
  | inv => exact Ival.mem_inv hx
  | exp => exact mem_fastExpIval c hx
  | sin => exact mem_fastSinIval hc hx
  | cos => exact mem_fastCosIval hc hx
  | sinh => exact mem_fastSinhIval c hx
  | cosh =>
    apply Ival.mem_clampLo (mem_fastCoshIval c hx)
    simpa [Dy.toReal_def] using Real.one_le_cosh x
  | log => exact mem_logIval hc hx
  | sqrt => exact Ival.mem_sqrt hx
  | abs => exact Ival.mem_abs hx
  | floor => exact mem_intFloor hx
  | atan => exact mem_atanIval hc hx

theorem binary_evalR_sound {c : Ctx} (_hc : c.Valid) (op : Binary)
    {x y : ℝ} {X Y : Ival} (hx : x ∈ X) (hy : y ∈ Y) :
    op.real x y ∈ Binary.evalR c op X Y := by
  cases op with
  | add => exact Ival.mem_add hx hy
  | sub => exact Ival.mem_sub hx hy
  | mul => exact mem_mulSigned hx hy
  | div => exact Ival.mem_div hx hy
  | max => exact Ival.mem_max hx hy
  | min => exact Ival.mem_min hx hy

theorem evalR_sound {c : Ctx} (hc : c.Valid) (e : Term)
    {x : ℝ} {X : Ival} (hx : x ∈ X) : e.real x ∈ evalR c e X := by
  induction e with
  | var => exact hx
  | rat q => exact Ival.mem_ofRat _ _
  | pi => exact hc.pi_mem
  | unary op a ih => exact unary_evalR_sound hc op ih
  | binary op a b ha hb =>
    change op.real (a.real x) (b.real x) ∈
      (if op = .sub ∧ b = .unary .floor a then fractionalIval c (evalR c a X)
       else Binary.evalR c op (evalR c a X) (evalR c b X))
    split
    · rename_i h
      obtain ⟨rfl,rfl⟩ := h
      exact mem_fractionalIval ha
    · exact binary_evalR_sound hc op ha hb
  | pow a n ih => exact mem_naturalPowerR ih n
  | rpow a q ih => exact mem_rationalPowerR hc ih q

def boundedComplexArg (Z : CBox) : Bool :=
  let bound := Dy.ofNat 16384
  match Z.re.lo,Z.re.hi,Z.im.lo,Z.im.hi with
  | some a,some b,some c,some d =>
    Dy.leB bound.neg a && Dy.leB b bound && Dy.leB bound.neg c && Dy.leB d bound
  | _,_,_,_ => false

/-- Trigonometric growth depends on the imaginary component. A large real
phase is harmless; only its representation size needs a work limit. -/
def boundedTrigArg (Z : CBox) : Bool :=
  match Z.re.lo, Z.re.hi with
  | some a, some b =>
    a.exponent.natAbs ≤ 16384 && b.exponent.natAbs ≤ 16384 &&
      boundedComplexArg ⟨Ival.zero,Z.im⟩
  | _, _ => false

def Unary.evalC (c : Ctx) (op : Unary) (Z : CBox) : CBox :=
  match op with
  | .neg => CBox.neg Z | .inv => CBox.inv c.prec Z
  | .exp => if boundedComplexArg Z then fastExpBox c Z else CBox.top
  | .sin => if boundedTrigArg Z then fastSinBox c Z else CBox.top
  | .cos => if boundedTrigArg Z then fastCosBox c Z else CBox.top
  | .sinh => if boundedComplexArg Z then sinhBox c Z else CBox.top
  | .cosh => if boundedComplexArg Z then coshBox c Z else CBox.top
  | .log => logBox c Z | .sqrt => sharedSqrtBox c Z
  | .abs => Z | .floor => CBox.ofReal Ival.zero | .atan => arctanC.ev c Z

def Binary.evalC (c : Ctx) (op : Binary) (X Y : CBox) : CBox :=
  match op with
  | .add => CBox.add c.prec X Y | .sub => CBox.sub c.prec X Y
  | .mul => CBox.mul c.prec X Y | .div => CBox.div c.prec X Y
  | .max | .min => X

def evalC (c : Ctx) (e : Term) (Z : CBox) : CBox :=
  match e with
  | .var => Z | .rat q => CBox.ofReal (Ival.ofRat c.prec q)
  | .pi => CBox.ofReal c.pi
  | .unary op a => Unary.evalC c op (evalC c a Z)
  | .binary op a b => Binary.evalC c op (evalC c a Z) (evalC c b Z)
  | .pow a n => naturalPowerC c.prec (evalC c a Z) n
  | .rpow a q => rationalPowerC c (evalC c a Z) q

theorem unary_evalC_sound {c : Ctx} (hc : c.Valid) (op : Unary)
    {z : ℂ} {Z : CBox} (hz : z ∈ Z) :
    op.complex z ∈ Unary.evalC c op Z := by
  cases op with
  | neg => exact CBox.mem_neg hz
  | inv => exact CBox.mem_inv hz
  | exp =>
    simp only [Unary.evalC]; split
    · exact mem_fastExpBox hc hz
    · exact CBox.mem_top _
  | sin =>
    simp only [Unary.evalC]; split
    · exact mem_fastSinBox hc hz
    · exact CBox.mem_top _
  | cos =>
    simp only [Unary.evalC]; split
    · exact mem_fastCosBox hc hz
    · exact CBox.mem_top _
  | sinh =>
    simp only [Unary.evalC]; split
    · exact mem_sinhBox c hc hz
    · exact CBox.mem_top _
  | cosh =>
    simp only [Unary.evalC]; split
    · exact mem_coshBox c hc hz
    · exact CBox.mem_top _
  | log => exact mem_logBox c hc hz
  | sqrt => exact mem_sharedSqrtBox c hc hz
  | abs => exact hz
  | floor => exact CBox.mem_ofReal Ival.mem_zero
  | atan => exact arctanC.sound c z _ Z hc rfl hz

theorem binary_evalC_sound {c : Ctx} (_hc : c.Valid) (op : Binary)
    {z w : ℂ} {Z W : CBox} (hz : z ∈ Z) (hw : w ∈ W) :
    op.complex z w ∈ Binary.evalC c op Z W := by
  cases op with
  | add => exact CBox.mem_add hz hw
  | sub => exact CBox.mem_sub hz hw
  | mul => exact CBox.mem_mul hz hw
  | div => exact CBox.mem_div hz hw
  | max => exact hz
  | min => exact hz

/-- The power kernel needs a nonzero input to use the exponential definition. -/
def regularCheck (c : Ctx) : Term → CBox → Bool
  | .var, _ | .rat _, _ | .pi, _ => true
  | .pow a _, Z => regularCheck c a Z
  | .rpow a _, Z => regularCheck c a Z && (evalC c a Z).re.pos
  | .unary op a, Z => regularCheck c a Z && match op with
      | .inv => (CBox.normSq c.prec (evalC c a Z)).pos
      | .log | .sqrt => (evalC c a Z).re.pos
      | .abs | .floor | .atan => false
      | _ => true
  | .binary op a b, Z => regularCheck c a Z && regularCheck c b Z && match op with
      | .div => (CBox.normSq c.prec (evalC c b Z)).pos
      | .max | .min => false
      | _ => true

theorem evalC_sound {c : Ctx} (hc : c.Valid) (e : Term) {Z : CBox}
    (hr : regularCheck c e Z = true) {z : ℂ} (hz : z ∈ Z) :
    e.complex z ∈ evalC c e Z := by
  induction e with
  | var => exact hz
  | rat q =>
    simpa only [Term.complex, evalC, Complex.ofReal_ratCast] using CBox.mem_ofReal (Ival.mem_ofRat c.prec q)
  | pi => exact CBox.mem_ofReal hc.pi_mem
  | unary op a ih =>
    exact unary_evalC_sound hc op (ih (Bool.and_eq_true_iff.mp hr).1)
  | binary op a b ha hb =>
    obtain ⟨hab, _⟩ := Bool.and_eq_true_iff.mp hr
    obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hab
    exact binary_evalC_sound hc op (ha hA) (hb hB)
  | pow a n ih => exact mem_naturalPowerC (ih hr) n
  | rpow a q ih =>
    obtain ⟨ha, hp⟩ := Bool.and_eq_true_iff.mp hr
    have hval := ih ha
    have hpos := Ival.pos_of hp hval.1
    have hne : a.complex z ≠ 0 := by intro h; simp [h] at hpos
    change a.complex z ^ ((q : ℝ) : ℂ) ∈ _
    exact mem_rationalPowerC hc hval hne q

theorem regularCheck_sound {c : Ctx} (hc : c.Valid) (e : Term) {Z : CBox}
    (h : regularCheck c e Z = true) : e.Regular {z | z ∈ Z} := by
  induction e with
  | var | rat | pi => trivial
  | pow a n ih => exact ih h
  | rpow a q ih =>
    obtain ⟨ha, hp⟩ := Bool.and_eq_true_iff.mp h
    exact ⟨ih ha, fun z hz => Ival.pos_of hp (evalC_sound hc a ha hz).1⟩
  | unary op a ih =>
    obtain ⟨ha, hop⟩ := Bool.and_eq_true_iff.mp h
    refine ⟨ih ha, ?_⟩
    cases op <;> try trivial
    · intro z hz he
      have hh := Ival.pos_of hop (CBox.mem_normSq (p := c.prec) (evalC_sound hc a ha hz))
      simp [he] at hh
    · exact fun z hz => Ival.pos_of hop (evalC_sound hc a ha hz).1
    · exact fun z hz => Ival.pos_of hop (evalC_sound hc a ha hz).1
    all_goals simp_all [regularCheck]
  | binary op a b ha hb =>
    obtain ⟨hab, hop⟩ := Bool.and_eq_true_iff.mp h
    obtain ⟨hA, hB⟩ := Bool.and_eq_true_iff.mp hab
    refine ⟨ha hA, hb hB, ?_⟩
    cases op <;> try trivial
    · intro z hz he
      have hh := Ival.pos_of hop (CBox.mem_normSq (p := c.prec) (evalC_sound hc b hB hz))
      simp [he] at hh
    all_goals simp_all [regularCheck]

end Lynth.Interval.Integral
