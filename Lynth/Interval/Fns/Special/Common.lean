import Lynth.Interval.Fns.Special.Kernel
import Lynth.Interval.Integral.Trig
import Lynth.Interval.Fns.Gamma

namespace Lynth.Interval.Fns

open SpecialFunctions

def specialSeriesR (p : ℕ) (kind : SeriesKind) (x : ℚ) : Ival :=
  match realSeriesBounds kind p x with
  | some (a,b) => ⟨some ⟨a,-(p : ℤ)⟩, some ⟨b,-(p : ℤ)⟩⟩
  | none => Ival.top

theorem mem_specialSeriesR (p : ℕ) (kind : SeriesKind) (x : ℚ) :
    seriesR kind (x : ℝ) ∈ specialSeriesR p kind x := by
  unfold specialSeriesR
  split
  · rename_i a b h
    simpa only [Ival.mem_mk, Ival.loLe_some, Ival.leHi_some, Dy.toReal_def,
      Dy.toRat_mk, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow, Rat.cast_ofNat] using
      realSeriesBounds_sound kind p x (a,b) h
  · exact Ival.mem_top _

def specialSeriesC (p : ℕ) (kind : SeriesKind) (re im : ℚ) : CBox :=
  match complexSeriesBounds kind p re im with
  | some ((a,b),(c,d)) =>
    ⟨⟨some ⟨a,-(p : ℤ)⟩,some ⟨b,-(p : ℤ)⟩⟩,
      ⟨some ⟨c,-(p : ℤ)⟩,some ⟨d,-(p : ℤ)⟩⟩⟩
  | none => CBox.top

theorem mem_specialSeriesC (p : ℕ) (kind : SeriesKind) (re im : ℚ) :
    seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I) ∈ specialSeriesC p kind re im := by
  unfold specialSeriesC
  split
  · rename_i a b c d h
    have hh := complexSeriesBounds_sound kind p re im ((a,b),(c,d)) h
    have h' := And.intro (And.intro hh.1 hh.2.1) hh.2.2
    simpa only [CBox.mem_def, Ival.mem_mk, Ival.loLe_some, Ival.leHi_some,
      Dy.toReal_def, Dy.toRat_mk, Rat.cast_mul, Rat.cast_intCast, Rat.cast_zpow,
      Rat.cast_ofNat] using h'
  · exact CBox.mem_top _

def specialWiden (p : ℕ) (X E : Ival) : Ival :=
  match E.hi with
  | some r => X.widen p r
  | none => Ival.top

theorem mem_specialWiden {p : ℕ} {x v e : ℝ} {X E : Ival}
    (hv : v ∈ X) (he : e ∈ E) (h : |x-v| ≤ e) : x ∈ specialWiden p X E := by
  unfold specialWiden
  split
  · rename_i r hr
    exact Ival.mem_widen hv (h.trans (he.2 r hr))
  · exact Ival.mem_top _

def specialWidenC (p : ℕ) (X : CBox) (E : Ival) : CBox :=
  ⟨specialWiden p X.re E, specialWiden p X.im E⟩

theorem mem_specialWidenC {p : ℕ} {z v : ℂ} {e : ℝ} {X : CBox} {E : Ival}
    (hv : v ∈ X) (he : e ∈ E) (h : ‖z-v‖ ≤ e) : z ∈ specialWidenC p X E := by
  exact ⟨mem_specialWiden hv.1 he ((Complex.abs_re_le_norm (z-v)).trans h),
    mem_specialWiden hv.2 he ((Complex.abs_im_le_norm (z-v)).trans h)⟩

/-- Work precision accounts for cancellation before the final enclosure is rounded. -/
def specialPrec (p : ℕ) (kind : SeriesKind) (r : ℚ) : ℕ :=
  let n := r.ceil.toNat
  p + 48 + match kind with
    | .erf => 2*n*n
    | .si => 2*n
    | .airy0 | .airy1 => 4*n*(n.sqrt+1)

/-- Exact rational complex arithmetic is used only once to form the series argument. -/
def specialPower (kind : SeriesKind) (a b : ℚ) : ℚ × ℚ :=
  match kind with
  | .erf | .si => (b*b-a*a,-2*a*b)
  | .airy0 | .airy1 => (a^3-3*a*b*b,3*a*a*b-b^3)

def rationalBox (p : ℕ) (a b : ℚ) : CBox := ⟨Ival.ofRat p a,Ival.ofRat p b⟩

theorem mem_rationalBox (p : ℕ) (a b : ℚ) :
    (a : ℂ)+(b : ℂ)*Complex.I ∈ rationalBox p a b := by
  constructor <;> simpa [rationalBox] using Ival.mem_ofRat p _

theorem specialPower_cast (kind : SeriesKind) (a b : ℚ) :
    ((specialPower kind a b).1 : ℂ) + ((specialPower kind a b).2 : ℂ)*Complex.I =
      match kind with
      | .erf | .si => -((a : ℂ)+(b : ℂ)*Complex.I)^2
      | .airy0 | .airy1 => ((a : ℂ)+(b : ℂ)*Complex.I)^3 := by
  cases kind <;> simp only [specialPower] <;> push_cast <;>
    ring_nf <;> simp [Complex.I_sq, Complex.I_pow_three] <;> ring

end Lynth.Interval.Fns
