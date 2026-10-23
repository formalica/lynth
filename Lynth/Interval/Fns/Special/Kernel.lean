module

public import Init.Data.Cast
public import Init.Data.Int.Basic
public import Init.Data.Int.Bitwise.Basic
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Nat.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Lynth.Analysis.SpecialFunctionsDefs
import all Lynth.Analysis.SpecialFunctions
import all Lynth.Analysis.SpecialFunctionsSeriesProofs

/-! Small portable fixed-point kernels. Real series use two integer endpoints;
complex series use four, in a distinct loop. No CBox, Ival or tactic dependencies.
Mirrored in /tmp/intgrl/SpecialKernel.lean (with its sole local import renamed).
-/

namespace SpecialFunctions

public abbrev Fixed := ℤ × ℤ
public abbrev FixedC := Fixed × Fixed

@[expose] public def fixedAdd (a b : Fixed) : Fixed := (a.1+b.1, a.2+b.2)
@[expose] public def fixedNeg (a : Fixed) : Fixed := (-a.2,-a.1)
@[expose] public def fixedMul (p : ℕ) (a b : Fixed) : Fixed :=
  let aa := a.1*b.1
  let ab := a.1*b.2
  let ba := a.2*b.1
  let bb := a.2*b.2
  (min (min aa ab) (min ba bb) >>> p,
    -((-max (max aa ab) (max ba bb)) >>> p))
@[expose] public def fixedScale (a : Fixed) (n d : ℕ) : Fixed :=
  (a.1 * (n : ℤ) / (d : ℤ), -((-a.2 * (n : ℤ)) / (d : ℤ)))
@[expose] public def fixedAbs (a : Fixed) : ℕ := max a.1.natAbs a.2.natAbs

@[expose] public def fixedCAdd (a b : FixedC) : FixedC := (fixedAdd a.1 b.1, fixedAdd a.2 b.2)
@[expose] public def fixedCMul (p : ℕ) (a b : FixedC) : FixedC :=
  (fixedAdd (fixedMul p a.1 b.1) (fixedNeg (fixedMul p a.2 b.2)),
    fixedAdd (fixedMul p a.1 b.2) (fixedMul p a.2 b.1))
@[expose] public def fixedCScale (a : FixedC) (n d : ℕ) : FixedC :=
  (fixedScale a.1 n d, fixedScale a.2 n d)
@[expose] public def fixedCAbs (a : FixedC) : ℕ := fixedAbs a.1 + fixedAbs a.2

@[expose] public def fixedInput (p : ℕ) (q : ℚ) : Fixed :=
  let q := q * ((2 : ℕ)^p : ℚ)
  (q.floor, q.ceil)

@[expose] public def realSeriesLoop (kind : SeriesKind) (p : ℕ) (x : Fixed) :
    ℕ → ℕ → Fixed → Fixed → Option Fixed
  | 0, _, _, _ => none
  | fuel+1, k, term, sum =>
    let sum := fixedAdd sum term
    let next := fixedScale (fixedMul p term x) (kind.num k) (kind.den k)
    if 2 * fixedAbs x * kind.num (k+1) ≤ 2^p * kind.den (k+1) &&
        fixedAbs next ≤ 4 then
      let err : ℤ := 2 * fixedAbs next
      some (sum.1-err, sum.2+err)
    else realSeriesLoop kind p x fuel (k+1) next sum

@[expose] public def complexSeriesLoop (kind : SeriesKind) (p : ℕ) (z : FixedC) :
    ℕ → ℕ → FixedC → FixedC → Option FixedC
  | 0, _, _, _ => none
  | fuel+1, k, term, sum =>
    let sum := fixedCAdd sum term
    let next := fixedCScale (fixedCMul p term z) (kind.num k) (kind.den k)
    if 2 * fixedCAbs z * kind.num (k+1) ≤ 2^p * kind.den (k+1) &&
        fixedCAbs next ≤ 8 then
      let err : ℤ := 2 * fixedCAbs next
      some ((sum.1.1-err, sum.1.2+err), (sum.2.1-err, sum.2.2+err))
    else complexSeriesLoop kind p z fuel (k+1) next sum

@[expose] public def realSeriesBounds (kind : SeriesKind) (p : ℕ) (x : ℚ) : Option Fixed :=
  realSeriesLoop kind p (fixedInput p x) (4*p+128) 0 (2^p,2^p) (0,0)

@[expose] public def complexSeriesBounds (kind : SeriesKind) (p : ℕ) (re im : ℚ) : Option FixedC :=
  complexSeriesLoop kind p (fixedInput p re, fixedInput p im) (4*p+128) 0
    ((2^p,2^p),(0,0)) ((0,0),(0,0))

private abbrev Encl (a : Fixed) (v : ℝ) : Prop := (a.1 : ℝ) ≤ v ∧ v ≤ a.2

private theorem encl_add {a b : Fixed} {u w : ℝ} (ha : Encl a u) (hb : Encl b w) :
    Encl (fixedAdd a b) (u + w) := by
  unfold Encl fixedAdd at *; push_cast; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]

private theorem encl_neg {a : Fixed} {u : ℝ} (ha : Encl a u) : Encl (fixedNeg a) (-u) := by
  unfold Encl fixedNeg at *; push_cast; constructor <;> linarith [ha.1, ha.2]

private theorem int_ediv_cast_le (x : ℤ) {d : ℤ} (hd : 0 < d) : ((x / d : ℤ) : ℝ) ≤ (x : ℝ) / d := by
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast Int.ediv_mul_le x hd.ne'

private theorem le_neg_ediv_neg_cast (x : ℤ) {d : ℤ} (hd : 0 < d) : (x : ℝ) / d ≤ ((-((-x) / d) : ℤ) : ℝ) := by
  have := int_ediv_cast_le (-x) hd
  push_cast at this ⊢
  rw [neg_div] at this
  linarith

private theorem mul_ge_min4 {a1 a2 b1 b2 u w : ℝ} (hu1 : a1 ≤ u) (hu2 : u ≤ a2) (hw1 : b1 ≤ w) (hw2 : w ≤ b2) :
    min (min (a1*b1) (a1*b2)) (min (a2*b1) (a2*b2)) ≤ u * w ∧
      u * w ≤ max (max (a1*b1) (a1*b2)) (max (a2*b1) (a2*b2)) := by
  constructor
  · rcases le_total 0 w with hw | hw
    · have h1 : a1 * w ≤ u * w := by nlinarith
      rcases le_total 0 a1 with ha | ha
      · have : a1 * b1 ≤ a1 * w := by nlinarith
        have := min_le_left (min (a1*b1) (a1*b2)) (min (a2*b1) (a2*b2))
        have := min_le_left (a1*b1) (a1*b2)
        linarith
      · have : a1 * b2 ≤ a1 * w := by nlinarith
        have := min_le_left (min (a1*b1) (a1*b2)) (min (a2*b1) (a2*b2))
        have := min_le_right (a1*b1) (a1*b2)
        linarith
    · have h1 : a2 * w ≤ u * w := by nlinarith
      rcases le_total 0 a2 with ha | ha
      · have : a2 * b1 ≤ a2 * w := by nlinarith
        have := min_le_right (min (a1*b1) (a1*b2)) (min (a2*b1) (a2*b2))
        have := min_le_left (a2*b1) (a2*b2)
        linarith
      · have : a2 * b2 ≤ a2 * w := by nlinarith
        have := min_le_right (min (a1*b1) (a1*b2)) (min (a2*b1) (a2*b2))
        have := min_le_right (a2*b1) (a2*b2)
        linarith
  · rcases le_total 0 w with hw | hw
    · have h1 : u * w ≤ a2 * w := by nlinarith
      rcases le_total 0 a2 with ha | ha
      · have : a2 * w ≤ a2 * b2 := by nlinarith
        have := le_max_right (max (a1*b1) (a1*b2)) (max (a2*b1) (a2*b2))
        have := le_max_right (a2*b1) (a2*b2)
        linarith
      · have : a2 * w ≤ a2 * b1 := by nlinarith
        have := le_max_right (max (a1*b1) (a1*b2)) (max (a2*b1) (a2*b2))
        have := le_max_left (a2*b1) (a2*b2)
        linarith
    · have h1 : u * w ≤ a1 * w := by nlinarith
      rcases le_total 0 a1 with ha | ha
      · have : a1 * w ≤ a1 * b2 := by nlinarith
        have := le_max_left (max (a1*b1) (a1*b2)) (max (a2*b1) (a2*b2))
        have := le_max_right (a1*b1) (a1*b2)
        linarith
      · have : a1 * w ≤ a1 * b1 := by nlinarith
        have := le_max_left (max (a1*b1) (a1*b2)) (max (a2*b1) (a2*b2))
        have := le_max_left (a1*b1) (a1*b2)
        linarith

private theorem encl_mul (p : ℕ) {a b : Fixed} {u w : ℝ} (ha : Encl a u) (hb : Encl b w) :
    Encl (fixedMul p a b) (u * w / 2^p) := by
  obtain ⟨h1, h2⟩ := mul_ge_min4 ha.1 ha.2 hb.1 hb.2
  have hd : (0:ℤ) < ((2^p : ℕ) : ℤ) := by positivity
  have hdR : (((2^p : ℕ) : ℤ) : ℝ) = (2:ℝ)^p := by push_cast; ring
  unfold fixedMul
  simp only [Int.shiftRight_eq_div_pow]
  constructor
  · refine (int_ediv_cast_le _ hd).trans ?_
    rw [hdR]
    gcongr
    push_cast
    exact h1
  · refine le_trans ?_ (le_neg_ediv_neg_cast _ hd)
    rw [hdR]
    gcongr
    push_cast
    exact h2

private theorem encl_scale {a : Fixed} {u : ℝ} (n d : ℕ) (hd : 0 < d) (ha : Encl a u) :
    Encl (fixedScale a n d) (u * n / d) := by
  have hd' : (0:ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  unfold fixedScale
  constructor
  · refine (int_ediv_cast_le _ hd').trans ?_
    push_cast
    gcongr
    exact ha.1
  · have := le_neg_ediv_neg_cast (a.2 * (n:ℤ)) hd'
    rw [show -(a.2 * (n:ℤ)) = -a.2 * (n:ℤ) by ring] at this
    refine le_trans ?_ this
    push_cast
    gcongr
    exact ha.2

private theorem encl_abs {a : Fixed} {v : ℝ} (ha : Encl a v) : |v| ≤ (fixedAbs a : ℝ) := by
  unfold fixedAbs
  rw [Nat.cast_max]
  have e1 : ((a.1.natAbs : ℕ) : ℝ) = |(a.1 : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have e2 : ((a.2.natAbs : ℕ) : ℝ) = |(a.2 : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  rw [e1, e2, abs_le]
  constructor
  · have := neg_abs_le (a.1 : ℝ)
    have := le_max_left |(a.1 : ℝ)| |(a.2 : ℝ)|
    linarith [ha.1]
  · have := le_abs_self (a.2 : ℝ)
    have := le_max_right |(a.1 : ℝ)| |(a.2 : ℝ)|
    linarith [ha.2]

private theorem rat_ceil_eq_ceil (x : ℚ) : x.ceil = ⌈x⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

private theorem encl_input (p : ℕ) (q : ℚ) : Encl (fixedInput p q) ((q : ℝ) * 2^p) := by
  unfold fixedInput Encl
  simp only
  have h1 := Int.floor_le (q * ((2:ℕ)^p : ℚ))
  have h2 := Int.le_ceil (q * ((2:ℕ)^p : ℚ))
  constructor
  · have : ((⌊q * ((2:ℕ)^p : ℚ)⌋ : ℚ) : ℝ) ≤ ((q * ((2:ℕ)^p : ℚ) : ℚ) : ℝ) := by exact_mod_cast h1
    push_cast at this ⊢; exact this
  · have : ((q * ((2:ℕ)^p : ℚ) : ℚ) : ℝ) ≤ ((⌈q * ((2:ℕ)^p : ℚ)⌉ : ℚ) : ℝ) := by exact_mod_cast h2
    rw [rat_ceil_eq_ceil]
    push_cast at this ⊢; exact this

private theorem ratio_succ_le (kind : SeriesKind) (j : ℕ) :
    (kind.num (j+1) : ℝ) / kind.den (j+1) ≤ kind.num j / kind.den j := by
  have h1 : (0:ℝ) < kind.den (j+1) := by exact_mod_cast den_pos kind (j+1)
  have h2 : (0:ℝ) < kind.den j := by exact_mod_cast den_pos kind j
  rw [div_le_div_iff₀ h1 h2]
  have hj : (0:ℝ) ≤ j := Nat.cast_nonneg j
  cases kind <;> simp only [SeriesKind.num, SeriesKind.den] <;> push_cast <;>
    nlinarith [pow_nonneg hj 2, pow_nonneg hj 3, pow_nonneg hj 4]

private theorem ratio_anti (kind : SeriesKind) {m j : ℕ} (h : m ≤ j) :
    (kind.num j : ℝ) / kind.den j ≤ kind.num m / kind.den m :=
  antitone_nat_of_succ_le (f := fun j => (kind.num j : ℝ) / kind.den j) (ratio_succ_le kind) h

private theorem norm_term_eq (kind : SeriesKind) (z : ℂ) (j : ℕ) :
    ‖(coefficient kind j : ℂ) * z ^ j‖ = (coefficient kind j : ℝ) * ‖z‖ ^ j := by
  rw [norm_mul, norm_pow, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by exact_mod_cast coefficient_nonneg kind j)]

private theorem term_succ_le (kind : SeriesKind) (z : ℂ) {m j : ℕ} (hmj : m ≤ j)
    (h : 2 * ‖z‖ * (kind.num m : ℝ) ≤ kind.den m) :
    ‖(coefficient kind (j+1) : ℂ) * z ^ (j+1)‖ ≤ ‖(coefficient kind j : ℂ) * z ^ j‖ / 2 := by
  rw [norm_term_eq, norm_term_eq]
  have hc : (coefficient kind (j+1) : ℝ) = coefficient kind j * (kind.num j / kind.den j) := by
    rw [show coefficient kind (j + 1) =
      coefficient kind j * kind.num j / kind.den j by rfl]
    push_cast; ring
  have hdm : (0:ℝ) < kind.den m := by exact_mod_cast den_pos kind m
  have hr := ratio_anti kind hmj
  have hzr : ‖z‖ * ((kind.num j : ℝ) / kind.den j) ≤ 1/2 := by
    calc ‖z‖ * ((kind.num j : ℝ) / kind.den j) ≤ ‖z‖ * ((kind.num m : ℝ) / kind.den m) := by
          gcongr
      _ ≤ 1/2 := by
          rw [mul_div_assoc', div_le_iff₀ hdm]; linarith
  have hc0 : (0:ℝ) ≤ coefficient kind j := by exact_mod_cast coefficient_nonneg kind j
  rw [hc, pow_succ]
  have hp : 0 ≤ (coefficient kind j : ℝ) * ‖z‖ ^ j := by positivity
  calc (coefficient kind j : ℝ) * (kind.num j / kind.den j) * (‖z‖ ^ j * ‖z‖)
      = ((coefficient kind j : ℝ) * ‖z‖ ^ j) * (‖z‖ * (kind.num j / kind.den j)) := by ring
    _ ≤ ((coefficient kind j : ℝ) * ‖z‖ ^ j) * (1/2) := by gcongr
    _ = _ := by ring

private theorem tail_bound (kind : SeriesKind) (z : ℂ) (m : ℕ)
    (h : 2 * ‖z‖ * (kind.num m : ℝ) ≤ kind.den m) :
    ‖seriesC kind z - ∑ j ∈ Finset.range m, (coefficient kind j : ℂ) * z ^ j‖ ≤
      2 * ‖(coefficient kind m : ℂ) * z ^ m‖ := by
  set f : ℕ → ℂ := fun j => (coefficient kind j : ℂ) * z ^ j with hf
  have hs : Summable f := summable_seriesC kind z
  have hsplit := hs.sum_add_tsum_nat_add m
  have hdiff : seriesC kind z - ∑ j ∈ Finset.range m, f j = ∑' i, f (i + m) := by
    rw [seriesC, ← hsplit]; ring
  rw [hdiff]
  have hb : ∀ i, ‖f (i + m)‖ ≤ ‖f m‖ * (1/2)^i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have := term_succ_le kind z (j := i + m) (by omega) h
      rw [show i + 1 + m = (i + m) + 1 by ring]
      calc ‖f (i + m + 1)‖ ≤ ‖f (i + m)‖ / 2 := this
        _ ≤ ‖f m‖ * (1/2)^i / 2 := by gcongr
        _ = _ := by ring
  have hg : HasSum (fun i : ℕ => ‖f m‖ * (1/2:ℝ)^i) (‖f m‖ * 2) :=
    hasSum_geometric_two.mul_left _
  calc ‖∑' i, f (i + m)‖ ≤ ‖f m‖ * 2 := tsum_of_norm_bounded hg hb
    _ = _ := by ring

private theorem tail_bound_real (kind : SeriesKind) (x : ℝ) (m : ℕ)
    (h : 2 * |x| * (kind.num m : ℝ) ≤ kind.den m) :
    |seriesR kind x - ∑ j ∈ Finset.range m, (coefficient kind j : ℝ) * x ^ j| ≤
      2 * |(coefficient kind m : ℝ) * x ^ m| := by
  have := tail_bound kind (x : ℂ) m (by rwa [Complex.norm_real, Real.norm_eq_abs])
  rw [seriesC_ofReal] at this
  have e1 : (seriesR kind x : ℂ) - ∑ j ∈ Finset.range m, (coefficient kind j : ℂ) * (x : ℂ) ^ j =
      ((seriesR kind x - ∑ j ∈ Finset.range m, (coefficient kind j : ℝ) * x ^ j : ℝ) : ℂ) := by
    push_cast; rfl
  have e2 : (coefficient kind m : ℂ) * (x : ℂ) ^ m = (((coefficient kind m : ℝ) * x ^ m : ℝ) : ℂ) := by
    push_cast; rfl
  rw [e1, e2, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs] at this
  exact this

private theorem realSeriesLoop_sound (kind : SeriesKind) (p : ℕ) (x : ℝ) (X : Fixed)
    (hX : Encl X (x * 2^p)) :
    ∀ (fuel k : ℕ) (term sum b : Fixed),
      Encl term ((coefficient kind k : ℝ) * x^k * 2^p) →
      Encl sum ((∑ j ∈ Finset.range k, (coefficient kind j : ℝ) * x^j) * 2^p) →
      realSeriesLoop kind p X fuel k term sum = some b →
      Encl b (seriesR kind x * 2^p) := by
  intro fuel
  induction fuel with
  | zero => intro k term sum b _ _ h; simp [realSeriesLoop] at h
  | succ fuel ih =>
    intro k term sum b hterm hsum h
    have hP : (0:ℝ) < 2^p := by positivity
    have hsum' : Encl (fixedAdd sum term)
        ((∑ j ∈ Finset.range (k+1), (coefficient kind j : ℝ) * x^j) * 2^p) := by
      have := encl_add hsum hterm
      rw [Finset.sum_range_succ]
      convert this using 1; ring
    have hnext : Encl (fixedScale (fixedMul p term X) (kind.num k) (kind.den k))
        ((coefficient kind (k+1) : ℝ) * x^(k+1) * 2^p) := by
      have := encl_scale (kind.num k) (kind.den k) (by exact_mod_cast den_pos kind k)
        (encl_mul p hterm hX)
      convert this using 1
      rw [show coefficient kind (k + 1) =
        coefficient kind k * kind.num k / kind.den k by rfl]
      have hd : (kind.den k : ℝ) ≠ 0 := by exact_mod_cast (den_pos kind k).ne'
      push_cast
      field_simp
      ring
    simp only [realSeriesLoop] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, -⟩ := hc
      have hxa : |x| * 2^p ≤ (fixedAbs X : ℝ) := by
        have := encl_abs hX
        rwa [abs_mul, abs_of_pos hP] at this
      have hc1' : (2 * (fixedAbs X : ℝ) * kind.num (k+1)) ≤ 2^p * kind.den (k+1) := by
        exact_mod_cast hc1
      have hcond : 2 * |x| * (kind.num (k+1) : ℝ) ≤ kind.den (k+1) := by
        have hn : (0:ℝ) ≤ kind.num (k+1) := Nat.cast_nonneg _
        have : 2^p * (2 * |x| * (kind.num (k+1) : ℝ)) ≤ 2^p * kind.den (k+1) := by
          nlinarith
        exact le_of_mul_le_mul_left this hP
      have ht := tail_bound_real kind x (k+1) hcond
      have hna := encl_abs hnext
      rw [abs_mul, abs_of_pos hP] at hna
      set S := ∑ j ∈ Finset.range (k+1), (coefficient kind j : ℝ) * x^j
      have habs := abs_le.1 ht
      obtain ⟨hs1, hs2⟩ := hsum'
      constructor
      · push_cast
        nlinarith
      · push_cast
        nlinarith
    · exact ih (k+1) _ _ b hnext hsum' h


/-- `a` encloses the (scaled) complex value `v` componentwise. -/
private abbrev EnclC (a : FixedC) (v : ℂ) : Prop := Encl a.1 v.re ∧ Encl a.2 v.im

private theorem enclC_add {a b : FixedC} {u w : ℂ} (ha : EnclC a u) (hb : EnclC b w) :
    EnclC (fixedCAdd a b) (u + w) := by
  refine ⟨?_, ?_⟩
  · rw [Complex.add_re]; exact encl_add ha.1 hb.1
  · rw [Complex.add_im]; exact encl_add ha.2 hb.2

private theorem enclC_mul (p : ℕ) {a b : FixedC} {u w : ℂ} (ha : EnclC a u) (hb : EnclC b w) :
    EnclC (fixedCMul p a b) (u * w / ((2^p : ℝ) : ℂ)) := by
  constructor
  · have := encl_add (encl_mul p ha.1 hb.1) (encl_neg (encl_mul p ha.2 hb.2))
    have e : (u * w / ((2^p : ℝ) : ℂ)).re =
        u.re * w.re / 2^p + -(u.im * w.im / 2^p) := by
      rw [Complex.div_ofReal_re, Complex.mul_re]; ring
    rw [e]; exact this
  · have := encl_add (encl_mul p ha.1 hb.2) (encl_mul p ha.2 hb.1)
    have e : (u * w / ((2^p : ℝ) : ℂ)).im =
        u.re * w.im / 2^p + u.im * w.re / 2^p := by
      rw [Complex.div_ofReal_im, Complex.mul_im]; ring
    rw [e]; exact this

private theorem enclC_scale {a : FixedC} {u : ℂ} (n d : ℕ) (hd : 0 < d) (ha : EnclC a u) :
    EnclC (fixedCScale a n d) (u * (((n : ℝ) / d : ℝ) : ℂ)) := by
  constructor
  · have := encl_scale n d hd ha.1
    have e : (u * (((n : ℝ) / d : ℝ) : ℂ)).re = u.re * n / d := by
      rw [Complex.re_mul_ofReal]; ring
    rw [e]; exact this
  · have := encl_scale n d hd ha.2
    have e : (u * (((n : ℝ) / d : ℝ) : ℂ)).im = u.im * n / d := by
      rw [Complex.im_mul_ofReal]; ring
    rw [e]; exact this

private theorem enclC_abs {a : FixedC} {v : ℂ} (ha : EnclC a v) : ‖v‖ ≤ (fixedCAbs a : ℝ) := by
  unfold fixedCAbs
  push_cast
  exact (Complex.norm_le_abs_re_add_abs_im v).trans (add_le_add (encl_abs ha.1) (encl_abs ha.2))

private theorem complexSeriesLoop_sound (kind : SeriesKind) (p : ℕ) (z : ℂ) (Z : FixedC)
    (hZ : EnclC Z (z * ((2^p : ℝ) : ℂ))) :
    ∀ (fuel k : ℕ) (term sum b : FixedC),
      EnclC term ((coefficient kind k : ℂ) * z^k * ((2^p : ℝ) : ℂ)) →
      EnclC sum ((∑ j ∈ Finset.range k, (coefficient kind j : ℂ) * z^j) * ((2^p : ℝ) : ℂ)) →
      complexSeriesLoop kind p Z fuel k term sum = some b →
      EnclC b (seriesC kind z * ((2^p : ℝ) : ℂ)) := by
  intro fuel
  induction fuel with
  | zero => intro k term sum b _ _ h; simp [complexSeriesLoop] at h
  | succ fuel ih =>
    intro k term sum b hterm hsum h
    have hP : (0:ℝ) < 2^p := by positivity
    have hPc : ((2^p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    have hsum' : EnclC (fixedCAdd sum term)
        ((∑ j ∈ Finset.range (k+1), (coefficient kind j : ℂ) * z^j) * ((2^p : ℝ) : ℂ)) := by
      have := enclC_add hsum hterm
      rw [Finset.sum_range_succ]
      convert this using 1; ring
    have hnext : EnclC (fixedCScale (fixedCMul p term Z) (kind.num k) (kind.den k))
        ((coefficient kind (k+1) : ℂ) * z^(k+1) * ((2^p : ℝ) : ℂ)) := by
      have := enclC_scale (kind.num k) (kind.den k) (by exact_mod_cast den_pos kind k)
        (enclC_mul p hterm hZ)
      convert this using 1
      rw [show coefficient kind (k + 1) =
        coefficient kind k * kind.num k / kind.den k by rfl]
      have hd : (kind.den k : ℂ) ≠ 0 := by exact_mod_cast (den_pos kind k).ne'
      push_cast
      field_simp
      ring
    simp only [complexSeriesLoop] at h
    split_ifs at h with hc
    · simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hc1, -⟩ := hc
      have hxa : ‖z‖ * 2^p ≤ (fixedCAbs Z : ℝ) := by
        have := enclC_abs hZ
        rwa [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP] at this
      have hc1' : (2 * (fixedCAbs Z : ℝ) * kind.num (k+1)) ≤ 2^p * kind.den (k+1) := by
        exact_mod_cast hc1
      have hcond : 2 * ‖z‖ * (kind.num (k+1) : ℝ) ≤ kind.den (k+1) := by
        have hn : (0:ℝ) ≤ kind.num (k+1) := Nat.cast_nonneg _
        have : 2^p * (2 * ‖z‖ * (kind.num (k+1) : ℝ)) ≤ 2^p * kind.den (k+1) := by
          nlinarith
        exact le_of_mul_le_mul_left this hP
      have ht := tail_bound kind z (k+1) hcond
      have hna := enclC_abs hnext
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP] at hna
      set S := ∑ j ∈ Finset.range (k+1), (coefficient kind j : ℂ) * z^j
      have hre := (Complex.abs_re_le_norm (seriesC kind z - S)).trans ht
      have him := (Complex.abs_im_le_norm (seriesC kind z - S)).trans ht
      rw [Complex.sub_re] at hre
      rw [Complex.sub_im] at him
      have hre' := abs_le.1 hre
      have him' := abs_le.1 him
      obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hsum'
      simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal] at h1 h2 h3 h4
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal] <;> push_cast <;> nlinarith
    · exact ih (k+1) _ _ b hnext hsum' h



theorem realSeriesBounds_sound (kind : SeriesKind) (p : ℕ) (x : ℚ) (b : Fixed)
    (h : realSeriesBounds kind p x = some b) :
    (b.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ seriesR kind x ∧
    seriesR kind x ≤ (b.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  unfold realSeriesBounds at h
  have hP : (0:ℝ) < 2^p := by positivity
  have hb := realSeriesLoop_sound kind p (x : ℝ) (fixedInput p x) (encl_input p x) _ 0 _ _ b
    (by simp [Encl, coefficient]) (by simp [Encl]) h
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, ← div_eq_mul_inv, div_le_iff₀ hP, le_div_iff₀ hP]
  exact hb

/-- Complex fixed-point series enclosure. -/

theorem complexSeriesBounds_sound (kind : SeriesKind) (p : ℕ) (re im : ℚ) (b : FixedC)
    (h : complexSeriesBounds kind p re im = some b) :
    (b.1.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).re ∧
    (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).re ≤ (b.1.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ∧
    (b.2.1 : ℝ) * (2 : ℝ)^(-(p : ℤ)) ≤ (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).im ∧
    (seriesC kind ((re : ℂ)+(im : ℂ)*Complex.I)).im ≤ (b.2.2 : ℝ) * (2 : ℝ)^(-(p : ℤ)) := by
  unfold complexSeriesBounds at h
  have hP : (0:ℝ) < 2^p := by positivity
  have hZ : EnclC (fixedInput p re, fixedInput p im)
      (((re : ℂ) + (im : ℂ) * Complex.I) * ((2^p : ℝ) : ℂ)) := by
    constructor
    · simp only [Complex.re_mul_ofReal]
      simpa using encl_input p re
    · simp only [Complex.im_mul_ofReal]
      simpa using encl_input p im
  have hb := complexSeriesLoop_sound kind p _ _ hZ _ 0 _ _ b
    (by
      simp only [EnclC, Encl, coefficient, pow_zero, Rat.cast_one, one_mul, mul_one,
        Complex.ofReal_re, Complex.ofReal_im]
      push_cast; simp) (by simp [EnclC, Encl]) h
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hb
  simp only [Complex.re_mul_ofReal, Complex.im_mul_ofReal] at h1 h2 h3 h4
  rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv, ← div_eq_mul_inv, ← div_eq_mul_inv,
    ← div_eq_mul_inv, div_le_iff₀ hP, le_div_iff₀ hP, div_le_iff₀ hP, le_div_iff₀ hP]
  exact ⟨h1, h2, h3, h4⟩

/-- Coarse derivative bounds on convex rectangles for transporting complex midpoints.
The l1 radius r bounds |Re z|+|Im z| on the full rectangle. -/
theorem complex_lipschitz (z w : ℂ) (r : ℝ) (hz : ‖z‖ ≤ r) (hw : ‖w‖ ≤ r) :
    ‖Complex.erf z - Complex.erf w‖ ≤ 2*Real.exp (r^2)*‖z-w‖ ∧
    ‖Complex.Si z - Complex.Si w‖ ≤ Real.exp r*‖z-w‖ ∧
    ‖Complex.airyAi z - Complex.airyAi w‖ ≤
      (2+r)^2*Real.exp (r^2+1)*‖z-w‖ := by

  have hconv : Convex ℝ (Metric.closedBall (0:ℂ) r) := convex_closedBall 0 r
  have hzs : z ∈ Metric.closedBall (0:ℂ) r := mem_closedBall_zero_iff.2 hz
  have hws : w ∈ Metric.closedBall (0:ℂ) r := mem_closedBall_zero_iff.2 hw
  refine ⟨?_, ?_, ?_⟩
  · exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).1.1.hasDerivWithinAt)
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).1.2) hws hzs
  · exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).2.1.1.hasDerivWithinAt)
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).2.1.2) hws hzs
  · exact hconv.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).2.2.1.hasDerivWithinAt)
      (fun ζ hζ => (complex_derivative_bounds ζ r
        (mem_closedBall_zero_iff.mp hζ)).2.2.2) hws hzs

theorem complex_lipschitz_pair (z w : ℂ) :
    ‖Complex.erf z - Complex.erf w‖ ≤ 2*Real.exp ((‖z‖+‖w‖)^2)*‖z-w‖ ∧
    ‖Complex.Si z - Complex.Si w‖ ≤ Real.exp (‖z‖+‖w‖)*‖z-w‖ ∧
    ‖Complex.airyAi z - Complex.airyAi w‖ ≤
      (2+‖z‖+‖w‖)^2*Real.exp ((‖z‖+‖w‖)^2+1)*‖z-w‖ := by
  simpa [add_assoc] using complex_lipschitz z w (‖z‖+‖w‖)
    (le_add_of_nonneg_right (norm_nonneg _)) (le_add_of_nonneg_left (norm_nonneg _))

end SpecialFunctions
