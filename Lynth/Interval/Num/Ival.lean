import Lynth.Interval.Num.Dy

/-!
# Extended real intervals

`Ival` has optional dyadic endpoints (`none` = ∓∞).  All operations are
sound for every input (they return `Ival.top` when unsure) and take the
precision `p` (mantissa bits) used for outward rounding.
See `docs/interval/02-numerics.md §2`.
-/

namespace Lynth.Interval

/-- Interval with extended dyadic endpoints: `lo = none` is `-∞`, `hi = none` is `+∞`. -/
structure Ival where
  lo : Option Dy
  hi : Option Dy
deriving Repr, Inhabited

namespace Ival

open Dy

/-- lower-end condition -/
def LoLe (lo : Option Dy) (x : ℝ) : Prop := ∀ l, lo = some l → l.toReal ≤ x
/-- upper-end condition -/
def LeHi (x : ℝ) (hi : Option Dy) : Prop := ∀ h, hi = some h → x ≤ h.toReal

@[simp] theorem loLe_none (x : ℝ) : LoLe none x := by simp [LoLe]
@[simp] theorem loLe_some (l : Dy) (x : ℝ) : LoLe (some l) x ↔ l.toReal ≤ x := by simp [LoLe]
@[simp] theorem leHi_none (x : ℝ) : LeHi x none := by simp [LeHi]
@[simp] theorem leHi_some (h : Dy) (x : ℝ) : LeHi x (some h) ↔ x ≤ h.toReal := by simp [LeHi]

/-- Membership of a real in an interval. -/
def Mem (I : Ival) (x : ℝ) : Prop := LoLe I.lo x ∧ LeHi x I.hi

instance : Membership ℝ Ival := ⟨Ival.Mem⟩

theorem mem_def {x : ℝ} {I : Ival} : x ∈ I ↔ LoLe I.lo x ∧ LeHi x I.hi := Iff.rfl

@[simp] theorem mem_mk {x : ℝ} {lo hi : Option Dy} :
    x ∈ (⟨lo, hi⟩ : Ival) ↔ LoLe lo x ∧ LeHi x hi := Iff.rfl

/-- The whole real line. -/
def top : Ival := ⟨none, none⟩
theorem mem_top (x : ℝ) : x ∈ top := by simp [top]

/-- A point. -/
def pt (d : Dy) : Ival := ⟨some d, some d⟩
theorem mem_pt (d : Dy) : d.toReal ∈ pt d := by simp [pt]

def zero : Ival := pt Dy.zero
def one : Ival := pt Dy.one
theorem mem_zero : (0 : ℝ) ∈ zero := by simp [zero, pt, toReal_def]
theorem mem_one : (1 : ℝ) ∈ one := by simp [one, pt, toReal_def]

/-- Interval enclosing a rational. -/
def ofRat (p : Nat) (q : ℚ) : Ival := ⟨some (ofRatD p q), some (ofRatU p q)⟩
theorem mem_ofRat (p : Nat) (q : ℚ) : (q : ℝ) ∈ ofRat p q := by
  simp only [ofRat, mem_mk, loLe_some, leHi_some, toReal_def]
  exact ⟨by exact_mod_cast ofRatD_le p q, by exact_mod_cast le_ofRatU p q⟩

/-- interval between two rationals (outward rounded) -/
def ofRats (p : Nat) (a b : ℚ) : Ival := ⟨some (ofRatD p a), some (ofRatU p b)⟩

theorem mem_ofRats {p : Nat} {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x ≤ (b : ℝ)) :
    x ∈ ofRats p a b := by
  simp only [ofRats, mem_mk, loLe_some, leHi_some, toReal_def]
  exact ⟨le_trans (Rat.cast_le.2 (ofRatD_le p a)) ha, le_trans hb (Rat.cast_le.2 (le_ofRatU p b))⟩

def isFinite (I : Ival) : Bool := I.lo.isSome && I.hi.isSome

/-! ### Helpers -/

/-- apply a binary endpoint function when both endpoints are finite -/
def omap2 (f : Dy → Dy → Dy) : Option Dy → Option Dy → Option Dy
  | some a, some b => some (f a b)
  | _, _ => none

theorem loLe_omap2 {f : Dy → Dy → Dy} {a b : Option Dy} {z : ℝ}
    (hf : ∀ u v, a = some u → b = some v → (f u v).toReal ≤ z)
    : LoLe (omap2 f a b) z := by
  intro l hl
  cases a <;> cases b <;> simp [omap2] at hl
  subst hl; exact hf _ _ rfl rfl

theorem leHi_omap2 {f : Dy → Dy → Dy} {a b : Option Dy} {z : ℝ}
    (hf : ∀ u v, a = some u → b = some v → z ≤ (f u v).toReal)
    : LeHi z (omap2 f a b) := by
  intro l hl
  cases a <;> cases b <;> simp [omap2] at hl
  subst hl; exact hf _ _ rfl rfl

/-! ### Addition, negation, subtraction -/

def add (p : Nat) (I J : Ival) : Ival := ⟨omap2 (addD p) I.lo J.lo, omap2 (addU p) I.hi J.hi⟩

theorem mem_add {p : Nat} {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) :
    x + y ∈ add p I J := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · refine loLe_omap2 ?_
    intro u v hu hv
    have h1 := hx1 u hu; have h2 := hy1 v hv
    have := addD_le p u v
    simp only [toReal_def] at *
    have : ((addD p u v).toRat : ℝ) ≤ (u.toRat : ℝ) + v.toRat := by exact_mod_cast this
    linarith
  · refine leHi_omap2 ?_
    intro u v hu hv
    have h1 := hx2 u hu; have h2 := hy2 v hv
    have := le_addU p u v
    simp only [toReal_def] at *
    have : (u.toRat : ℝ) + v.toRat ≤ ((addU p u v).toRat : ℝ) := by exact_mod_cast this
    linarith

def neg (I : Ival) : Ival := ⟨I.hi.map Vendor.Dyadic.neg, I.lo.map Vendor.Dyadic.neg⟩

theorem mem_neg {x : ℝ} {I : Ival} (hx : x ∈ I) : -x ∈ neg I := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases I with ⟨lo, hi⟩
  refine ⟨?_, ?_⟩
  · cases hi with
    | none => simp [neg]
    | some b =>
      have := hx2 b rfl
      simp only [neg, Option.map_some, loLe_some, toReal_def, toRat_neg', Rat.cast_neg]
      simp only [toReal_def] at this; linarith
  · cases lo with
    | none => simp [neg]
    | some a =>
      have := hx1 a rfl
      simp only [neg, Option.map_some, leHi_some, toReal_def, toRat_neg', Rat.cast_neg]
      simp only [toReal_def] at this; linarith

def sub (p : Nat) (I J : Ival) : Ival := add p I (neg J)

theorem mem_sub {p : Nat} {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) :
    x - y ∈ sub p I J := by
  rw [sub_eq_add_neg]; exact mem_add hx (mem_neg hy)

/-! ### Multiplication -/

/-- lower end is a nonnegative number -/
def nonneg (I : Ival) : Bool := match I.lo with | some a => isNonneg a | none => false
/-- upper end is a nonpositive number -/
def nonpos (I : Ival) : Bool := match I.hi with | some b => isNonneg b.neg | none => false

theorem nonneg_of {I : Ival} {x : ℝ} (h : I.nonneg = true) (hx : x ∈ I) : 0 ≤ x := by
  unfold nonneg at h
  cases hl : I.lo with
  | none => simp [hl] at h
  | some a =>
    simp only [hl] at h
    have ha := (isNonneg_iff a).1 h
    have := hx.1 a hl
    simp only [toReal_def] at this
    have : (0 : ℝ) ≤ (a.toRat : ℝ) := by exact_mod_cast ha
    linarith

theorem neg_nonneg_of_nonpos {I : Ival} (h : I.nonpos = true) : (neg I).nonneg = true := by
  unfold nonpos at h; unfold nonneg neg
  cases hh : I.hi with
  | none => simp [hh] at h
  | some b => simp only [hh] at h; simpa using h

/-- product of intervals with nonnegative lower ends -/
def mulNN (p : Nat) (I J : Ival) : Ival :=
  ⟨omap2 (mulD p) I.lo J.lo, omap2 (mulU p) I.hi J.hi⟩

theorem mem_mulNN {p : Nat} {x y : ℝ} {I J : Ival} (hI : I.nonneg = true) (hJ : J.nonneg = true)
    (hx : x ∈ I) (hy : y ∈ J) : x * y ∈ mulNN p I J := by
  have hx0 := nonneg_of hI hx; have hy0 := nonneg_of hJ hy
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  refine ⟨?_, ?_⟩
  · refine loLe_omap2 ?_
    intro u v hu hv
    have h1 := hx1 u hu; have h2 := hy1 v hv
    have hu0 : 0 ≤ u.toReal := by
      unfold nonneg at hI; rw [hu] at hI
      simp only [toReal_def]; exact_mod_cast (isNonneg_iff u).1 hI
    have := mulD_le p u v
    simp only [toReal_def] at *
    have h3 : ((mulD p u v).toRat : ℝ) ≤ (u.toRat : ℝ) * v.toRat := by exact_mod_cast this
    have h4 : (u.toRat : ℝ) * v.toRat ≤ x * y := mul_le_mul h1 h2 (by
      unfold nonneg at hJ; rw [hv] at hJ; exact_mod_cast (isNonneg_iff v).1 hJ) hx0
    linarith
  · refine leHi_omap2 ?_
    intro u v hu hv
    have h1 := hx2 u hu; have h2 := hy2 v hv
    have := le_mulU p u v
    simp only [toReal_def] at *
    have h3 : (u.toRat : ℝ) * v.toRat ≤ ((mulU p u v).toRat : ℝ) := by exact_mod_cast this
    have h4 : x * y ≤ (u.toRat : ℝ) * v.toRat := mul_le_mul h1 h2 hy0 (le_trans hx0 h1)
    linarith

private theorem mul_mem_endpoints_left {x a₁ a₂ y : ℝ} (ha : a₁ ≤ x ∧ x ≤ a₂) :
    min (a₁ * y) (a₂ * y) ≤ x * y ∧ x * y ≤ max (a₁ * y) (a₂ * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right ha.1 hy),
      le_trans (mul_le_mul_of_nonneg_right ha.2 hy) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right ha.2 hy),
      le_trans (mul_le_mul_of_nonpos_right ha.1 hy) (le_max_left _ _)⟩

private theorem mul_mem_endpoints_right {y b₁ b₂ x : ℝ} (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (x * b₁) (x * b₂) ≤ x * y ∧ x * y ≤ max (x * b₁) (x * b₂) := by
  rcases le_total 0 x with hx | hx
  · exact ⟨le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hb.1 hx),
      le_trans (mul_le_mul_of_nonneg_left hb.2 hx) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hb.2 hx),
      le_trans (mul_le_mul_of_nonpos_left hb.1 hx) (le_max_left _ _)⟩

/-- corner lemma: `xy` lies between the extreme corner products -/
theorem mul_mem_corners {x y a₁ a₂ b₁ b₂ : ℝ} (ha : a₁ ≤ x ∧ x ≤ a₂) (hb : b₁ ≤ y ∧ y ≤ b₂) :
    min (min (a₁ * b₁) (a₁ * b₂)) (min (a₂ * b₁) (a₂ * b₂)) ≤ x * y ∧
    x * y ≤ max (max (a₁ * b₁) (a₁ * b₂)) (max (a₂ * b₁) (a₂ * b₂)) := by
  have h1 := mul_mem_endpoints_left (y := y) ha
  have hr1 := mul_mem_endpoints_right hb (x := a₁)
  have hr2 := mul_mem_endpoints_right hb (x := a₂)
  constructor
  · rcases le_total (a₁ * y) (a₂ * y) with h | h
    · rw [min_eq_left h] at h1
      exact le_trans (min_le_left _ _) (le_trans hr1.1 h1.1)
    · rw [min_eq_right h] at h1
      exact le_trans (min_le_right _ _) (le_trans hr2.1 h1.1)
  · rcases le_total (a₁ * y) (a₂ * y) with h | h
    · rw [max_eq_right h] at h1
      exact le_trans (le_trans h1.2 hr2.2) (le_max_right _ _)
    · rw [max_eq_left h] at h1
      exact le_trans (le_trans h1.2 hr1.2) (le_max_left _ _)

/-- product of finite intervals by the four corners -/
def mulFin (p : Nat) (a b c d : Dy) : Ival :=
  ⟨some (Dy.min (Dy.min (mulD p a c) (mulD p a d)) (Dy.min (mulD p b c) (mulD p b d))),
   some (Dy.max (Dy.max (mulU p a c) (mulU p a d)) (Dy.max (mulU p b c) (mulU p b d)))⟩

theorem min_toReal_le_left (u v : Dy) : (Dy.min u v).toReal ≤ u.toReal := by
  simp only [toReal_def]; exact_mod_cast toRat_min_le_left u v
theorem min_toReal_le_right (u v : Dy) : (Dy.min u v).toReal ≤ v.toReal := by
  simp only [toReal_def]; exact_mod_cast toRat_min_le_right u v
theorem le_max_toReal_left (u v : Dy) : u.toReal ≤ (Dy.max u v).toReal := by
  simp only [toReal_def]; exact_mod_cast le_toRat_max_left u v
theorem le_max_toReal_right (u v : Dy) : v.toReal ≤ (Dy.max u v).toReal := by
  simp only [toReal_def]; exact_mod_cast le_toRat_max_right u v

private theorem mulD_toReal (p) (u v : Dy) : (mulD p u v).toReal ≤ u.toReal * v.toReal := by
  simp only [toReal_def]; exact_mod_cast mulD_le p u v
private theorem mulU_toReal (p) (u v : Dy) : u.toReal * v.toReal ≤ (mulU p u v).toReal := by
  simp only [toReal_def]; exact_mod_cast le_mulU p u v

theorem mem_mulFin {p : Nat} {x y : ℝ} {a b c d : Dy}
    (hx : a.toReal ≤ x ∧ x ≤ b.toReal) (hy : c.toReal ≤ y ∧ y ≤ d.toReal) :
    x * y ∈ mulFin p a b c d := by
  have hc := mul_mem_corners hx hy
  simp only [mulFin, mem_mk, loLe_some, leHi_some]
  constructor
  · refine le_trans ?_ hc.1
    refine le_min (le_min ?_ ?_) (le_min ?_ ?_)
    · exact le_trans (min_toReal_le_left _ _) (le_trans (min_toReal_le_left _ _) (mulD_toReal p a c))
    · exact le_trans (min_toReal_le_left _ _) (le_trans (min_toReal_le_right _ _) (mulD_toReal p a d))
    · exact le_trans (min_toReal_le_right _ _) (le_trans (min_toReal_le_left _ _) (mulD_toReal p b c))
    · exact le_trans (min_toReal_le_right _ _) (le_trans (min_toReal_le_right _ _) (mulD_toReal p b d))
  · refine le_trans hc.2 ?_
    refine max_le (max_le ?_ ?_) (max_le ?_ ?_)
    · exact le_trans (mulU_toReal p a c) (le_trans (le_max_toReal_left _ _) (le_max_toReal_left _ _))
    · exact le_trans (mulU_toReal p a d) (le_trans (le_max_toReal_right _ _) (le_max_toReal_left _ _))
    · exact le_trans (mulU_toReal p b c) (le_trans (le_max_toReal_left _ _) (le_max_toReal_right _ _))
    · exact le_trans (mulU_toReal p b d) (le_trans (le_max_toReal_right _ _) (le_max_toReal_right _ _))

/-- Interval product (sound for extended intervals). -/
def mul (p : Nat) (I J : Ival) : Ival :=
  if I.nonneg && J.nonneg then mulNN p I J else
  match I, J with
  | ⟨some a, some b⟩, ⟨some c, some d⟩ => mulFin p a b c d
  | I, J =>
    if I.nonneg && J.nonneg then mulNN p I J
    else if I.nonpos && J.nonneg then neg (mulNN p (neg I) J)
    else if I.nonneg && J.nonpos then neg (mulNN p I (neg J))
    else if I.nonpos && J.nonpos then mulNN p (neg I) (neg J)
    else top

theorem mem_mul {p : Nat} {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) :
    x * y ∈ mul p I J := by
  have generic : x * y ∈
      (if I.nonneg && J.nonneg then mulNN p I J
       else if I.nonpos && J.nonneg then neg (mulNN p (neg I) J)
       else if I.nonneg && J.nonpos then neg (mulNN p I (neg J))
       else if I.nonpos && J.nonpos then mulNN p (neg I) (neg J)
       else top) := by
    split
    · rename_i h; simp only [Bool.and_eq_true] at h
      exact mem_mulNN h.1 h.2 hx hy
    split
    · rename_i _ h; simp only [Bool.and_eq_true] at h
      have := mem_mulNN (p := p) (neg_nonneg_of_nonpos h.1) h.2 (mem_neg hx) hy
      simpa using mem_neg this
    split
    · rename_i _ _ h; simp only [Bool.and_eq_true] at h
      have := mem_mulNN (p := p) h.1 (neg_nonneg_of_nonpos h.2) hx (mem_neg hy)
      simpa using mem_neg this
    split
    · rename_i _ _ _ h; simp only [Bool.and_eq_true] at h
      have := mem_mulNN (p := p) (neg_nonneg_of_nonpos h.1) (neg_nonneg_of_nonpos h.2)
        (mem_neg hx) (mem_neg hy)
      simpa using this
    · exact mem_top _
  unfold mul
  split
  · rename_i h; simp only [Bool.and_eq_true] at h
    exact mem_mulNN h.1 h.2 hx hy
  split
  · rename_i a b c d _
    obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
    exact mem_mulFin ⟨hx1 a rfl, hx2 b rfl⟩ ⟨hy1 c rfl, hy2 d rfl⟩
  · exact generic

/-- Square (dependency-aware). -/
def sq (p : Nat) (I : Ival) : Ival :=
  if I.nonneg then mulNN p I I
  else if I.nonpos then mulNN p (neg I) (neg I)
  else
    match I.lo, I.hi with
    | some a, some b =>
      ⟨some Dy.zero, some (Dy.max (mulU p a a) (mulU p b b))⟩
    | _, _ => ⟨some Dy.zero, none⟩

theorem mem_sq {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) : x ^ 2 ∈ sq p I := by
  unfold sq
  split
  · rename_i h; rw [pow_two]; exact mem_mulNN h h hx hx
  split
  · rename_i _ h
    have := mem_mulNN (p := p) (neg_nonneg_of_nonpos h) (neg_nonneg_of_nonpos h) (mem_neg hx) (mem_neg hx)
    simpa [pow_two] using this
  · obtain ⟨hx1, hx2⟩ := hx
    split
    · rename_i a b ha hb
      simp only [mem_mk, loLe_some, leHi_some, toReal_def, toRat_zero, Rat.cast_zero]
      refine ⟨sq_nonneg x, ?_⟩
      have h1 := hx1 a ha; have h2 := hx2 b hb
      simp only [toReal_def] at h1 h2
      have ha' : ((a.toRat : ℝ) * a.toRat) ≤ ((mulU p a a).toRat : ℝ) := by exact_mod_cast le_mulU p a a
      have hb' : ((b.toRat : ℝ) * b.toRat) ≤ ((mulU p b b).toRat : ℝ) := by exact_mod_cast le_mulU p b b
      have hmax1 : ((mulU p a a).toRat : ℝ) ≤ ((Dy.max (mulU p a a) (mulU p b b)).toRat : ℝ) := by
        exact_mod_cast le_toRat_max_left _ _
      have hmax2 : ((mulU p b b).toRat : ℝ) ≤ ((Dy.max (mulU p a a) (mulU p b b)).toRat : ℝ) := by
        exact_mod_cast le_toRat_max_right _ _
      rcases le_total 0 x with h0 | h0
      · have : x ^ 2 ≤ (b.toRat : ℝ) * b.toRat := by nlinarith
        linarith
      · have : x ^ 2 ≤ (a.toRat : ℝ) * a.toRat := by nlinarith
        linarith
    · simp only [mem_mk, loLe_some, leHi_none, toReal_def, toRat_zero, Rat.cast_zero, and_true]
      exact sq_nonneg x

/-- Natural power (binary powering with dependency-aware squaring; fuel bounds the depth). -/
def npowAux (p : Nat) (I : Ival) : Nat → Nat → Ival
  | 0, _ => top
  | _ + 1, 0 => one
  | _ + 1, 1 => I
  | fuel + 1, n + 2 =>
    if n % 2 = 0 then sq p (npowAux p I fuel ((n + 2) / 2))
    else mul p I (npowAux p I fuel (n + 1))

/-- fuel `130` covers every exponent `< 2^64` (at most `2·log₂ n + 2` steps) -/
def npow (p : Nat) (I : Ival) (n : Nat) : Ival := npowAux p I 130 n

theorem mem_npowAux {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) :
    ∀ fuel n, x ^ n ∈ npowAux p I fuel n
  | 0, _ => mem_top _
  | _ + 1, 0 => by simpa [npowAux] using mem_one
  | _ + 1, 1 => by simpa [npowAux] using hx
  | fuel + 1, n + 2 => by
    unfold npowAux
    split
    · rename_i h
      have := mem_sq (p := p) (mem_npowAux (p := p) (I := I) hx fuel ((n + 2) / 2))
      rw [← pow_mul] at this
      have hn : (n + 2) / 2 * 2 = n + 2 := by omega
      rwa [hn] at this
    · have := mem_mul (p := p) hx (mem_npowAux (p := p) (I := I) hx fuel (n + 1))
      rwa [← pow_succ'] at this

theorem mem_npow {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) (n : Nat) : x ^ n ∈ npow p I n :=
  mem_npowAux hx _ n

/-! ### Inverse and division -/

/-- lower end is a positive number -/
def pos (I : Ival) : Bool := match I.lo with | some a => isPos a | none => false
/-- upper end is a negative number -/
def negv (I : Ival) : Bool := match I.hi with | some b => isNeg b | none => false

theorem pos_of {I : Ival} {x : ℝ} (h : I.pos = true) (hx : x ∈ I) : 0 < x := by
  unfold pos at h
  cases hl : I.lo with
  | none => simp [hl] at h
  | some a =>
    simp only [hl] at h
    have ha := (isPos_iff a).1 h
    have := hx.1 a hl
    simp only [toReal_def] at this
    have : (0 : ℝ) < (a.toRat : ℝ) := by exact_mod_cast ha
    linarith

theorem neg_of {I : Ival} {x : ℝ} (h : I.negv = true) (hx : x ∈ I) : x < 0 := by
  unfold negv at h
  cases hl : I.hi with
  | none => simp [hl] at h
  | some b =>
    simp only [hl] at h
    have hb := (isNeg_iff b).1 h
    have := hx.2 b hl
    simp only [toReal_def] at this
    have : (b.toRat : ℝ) < 0 := by exact_mod_cast hb
    linarith

/-- lower bound of `1/b` as a real -/
private theorem divD_one_toReal {p : Nat} {b : Dy} (hb : b.toReal ≠ 0) :
    (divD p Dy.one b).toReal ≤ 1 / b.toReal := by
  have h1 := divD_le p Dy.one b (by intro h; apply hb; simp [toReal_def, h])
  simp only [toRat_one] at h1
  simp only [toReal_def] at hb ⊢
  exact_mod_cast h1

private theorem divU_one_toReal {p : Nat} {b : Dy} (hb : b.toReal ≠ 0) :
    1 / b.toReal ≤ (divU p Dy.one b).toReal := by
  have h1 := le_divU p Dy.one b (by intro h; apply hb; simp [toReal_def, h])
  simp only [toRat_one] at h1
  simp only [toReal_def] at hb ⊢
  exact_mod_cast h1

/-- `1/x` (Mathlib: `0⁻¹ = 0`); `top` if the interval may contain `0`. -/
def inv (p : Nat) (I : Ival) : Ival :=
  if I.pos then
    ⟨some (match I.hi with | some b => divD p Dy.one b | none => Dy.zero),
     some (match I.lo with | some a => divU p Dy.one a | none => Dy.zero)⟩
  else if I.negv then
    ⟨some (match I.hi with | some b => divD p Dy.one b | none => Dy.zero),
     some (match I.lo with | some a => divU p Dy.one a | none => Dy.zero)⟩
  else top

theorem mem_inv {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) : x⁻¹ ∈ inv p I := by
  unfold inv
  split
  · rename_i hpos
    have hxpos := pos_of hpos hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [mem_mk, loLe_some, leHi_some]
    constructor
    · split
      · rename_i b hb
        have hxb : x ≤ b.toReal := hx2 b hb
        have hbpos : 0 < b.toReal := lt_of_lt_of_le hxpos hxb
        refine le_trans (divD_one_toReal (ne_of_gt hbpos)) ?_
        rw [one_div]; exact inv_anti₀ hxpos hxb
      · simp only [toReal_def, toRat_zero, Rat.cast_zero]; exact le_of_lt (inv_pos.2 hxpos)
    · split
      · rename_i a ha
        have hax : a.toReal ≤ x := hx1 a ha
        have hapos : 0 < a.toReal := by
          unfold pos at hpos; rw [ha] at hpos
          simp only [toReal_def]; exact_mod_cast (isPos_iff a).1 hpos
        refine le_trans ?_ (divU_one_toReal (ne_of_gt hapos))
        rw [one_div]; exact inv_anti₀ hapos hax
      · rename_i hl; unfold pos at hpos; rw [hl] at hpos; simp at hpos
  split
  · rename_i _ hneg
    have hxneg := neg_of hneg hx
    obtain ⟨hx1, hx2⟩ := hx
    simp only [mem_mk, loLe_some, leHi_some]
    constructor
    · split
      · rename_i b hb
        have hxb : x ≤ b.toReal := hx2 b hb
        have hbneg : b.toReal < 0 := by
          unfold negv at hneg; rw [hb] at hneg
          simp only [toReal_def]; exact_mod_cast (isNeg_iff b).1 hneg
        refine le_trans (divD_one_toReal (ne_of_lt hbneg)) ?_
        rw [one_div]; exact (inv_le_inv_of_neg hbneg hxneg).2 hxb
      · rename_i hh; unfold negv at hneg; rw [hh] at hneg; simp at hneg
    · split
      · rename_i a ha
        have hax : a.toReal ≤ x := hx1 a ha
        have haneg : a.toReal < 0 := lt_of_le_of_lt hax hxneg
        refine le_trans ?_ (divU_one_toReal (ne_of_lt haneg))
        rw [one_div]; exact (inv_le_inv_of_neg hxneg haneg).2 hax
      · simp only [toReal_def, toRat_zero, Rat.cast_zero]; exact le_of_lt (inv_lt_zero.2 hxneg)
  · exact mem_top _

/-- quotient, with a direct fast path for `I ≥ 0`, `J > 0` (finite) -/
def div (p : Nat) (I J : Ival) : Ival :=
  match I, J with
  | ⟨some a, some b⟩, ⟨some c, some d⟩ =>
    if isNonneg a && isPos c then ⟨some (divD p a d), some (divU p b c)⟩
    else mul p ⟨some a, some b⟩ (inv p ⟨some c, some d⟩)
  | I, J => mul p I (inv p J)

theorem mem_div {p : Nat} {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) :
    x / y ∈ div p I J := by
  unfold div
  split
  · rename_i a b c d
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      have ha0 : (0 : ℝ) ≤ a.toReal := by simp only [toReal_def]; exact_mod_cast (isNonneg_iff a).1 h.1
      have hc0 : (0 : ℝ) < c.toReal := by simp only [toReal_def]; exact_mod_cast (isPos_iff c).1 h.2
      have hax := hx.1 a rfl; have hxb := hx.2 b rfl
      have hcy := hy.1 c rfl; have hyd := hy.2 d rfl
      have hy0 : 0 < y := lt_of_lt_of_le hc0 hcy
      have hd0 : 0 < d.toReal := lt_of_lt_of_le hy0 hyd
      have hx0 : 0 ≤ x := le_trans ha0 hax
      have h1 : (divD p a d).toReal ≤ a.toReal / d.toReal := by
        have := divD_le p a d (by
          intro h0; have : d.toReal = 0 := by simp [toReal_def, h0]
          linarith)
        simp only [toReal_def]; exact_mod_cast this
      have h2 : b.toReal / c.toReal ≤ (divU p b c).toReal := by
        have := le_divU p b c (by
          intro h0; have : c.toReal = 0 := by simp [toReal_def, h0]
          linarith)
        simp only [toReal_def]; exact_mod_cast this
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · cases hl
        refine le_trans h1 ?_
        rw [div_le_div_iff₀ hd0 hy0]; nlinarith
      · cases hu
        refine le_trans ?_ h2
        rw [div_le_div_iff₀ hy0 hc0]; nlinarith
    · rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy)
  · rw [div_eq_mul_inv]; exact mem_mul hx (mem_inv hy)

/-! ### Order-based operations -/

def omin (a b : Option Dy) : Option Dy := omap2 Dy.min a b
def omax (a b : Option Dy) : Option Dy := omap2 Dy.max a b

/-- hull of two intervals -/
def hull (I J : Ival) : Ival := ⟨omin I.lo J.lo, omax I.hi J.hi⟩

theorem mem_hull_left {x : ℝ} {I J : Ival} (hx : x ∈ I) : x ∈ hull I J := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨loLe_omap2 ?_, leHi_omap2 ?_⟩
  · intro u v hu _; exact le_trans (min_toReal_le_left u v) (hx1 u hu)
  · intro u v hu _; exact le_trans (hx2 u hu) (le_max_toReal_left u v)

theorem mem_hull_right {x : ℝ} {I J : Ival} (hx : x ∈ J) : x ∈ hull I J := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨loLe_omap2 ?_, leHi_omap2 ?_⟩
  · intro u v _ hv; exact le_trans (min_toReal_le_right u v) (hx1 v hv)
  · intro u v _ hv; exact le_trans (hx2 v hv) (le_max_toReal_right u v)

/-- `max` of two intervals -/
def max (I J : Ival) : Ival := ⟨omax I.lo J.lo, omax I.hi J.hi⟩
/-- `min` of two intervals -/
def min (I J : Ival) : Ival := ⟨omin I.lo J.lo, omin I.hi J.hi⟩

theorem mem_max {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) : Max.max x y ∈ max I J := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  refine ⟨loLe_omap2 ?_, leHi_omap2 ?_⟩
  · intro u v hu hv
    rcases Dy.toRat_max_eq_or u v with h | h <;> rw [h]
    · exact le_trans (hx1 u hu) (le_max_left _ _)
    · exact le_trans (hy1 v hv) (le_max_right _ _)
  · intro u v hu hv
    exact max_le (le_trans (hx2 u hu) (le_max_toReal_left u v)) (le_trans (hy2 v hv) (le_max_toReal_right u v))

theorem mem_min {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) : Min.min x y ∈ min I J := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  refine ⟨loLe_omap2 ?_, leHi_omap2 ?_⟩
  · intro u v hu hv
    exact le_min (le_trans (min_toReal_le_left u v) (hx1 u hu)) (le_trans (min_toReal_le_right u v) (hy1 v hv))
  · intro u v hu hv
    rcases Dy.toRat_min_eq_or u v with h | h <;> rw [h]
    · exact le_trans (min_le_left _ _) (hx2 u hu)
    · exact le_trans (min_le_right _ _) (hy2 v hv)

/-- absolute value -/
def abs (I : Ival) : Ival :=
  if I.nonneg then I
  else if I.nonpos then neg I
  else ⟨some Dy.zero, omax (I.hi) (I.lo.map Vendor.Dyadic.neg)⟩

theorem mem_abs {x : ℝ} {I : Ival} (hx : x ∈ I) : |x| ∈ abs I := by
  unfold abs
  split
  · rename_i h; rwa [abs_of_nonneg (nonneg_of h hx)]
  split
  · rename_i _ h
    have := nonneg_of (neg_nonneg_of_nonpos h) (mem_neg hx)
    rw [abs_of_nonpos (by linarith)]; exact mem_neg hx
  · obtain ⟨hx1, hx2⟩ := hx
    refine ⟨by simp [toReal_def, abs_nonneg], leHi_omap2 ?_⟩
    intro u v hu hv
    cases hl : I.lo <;> simp [hl] at hv
    subst hv
    have h1 := hx2 u hu; have h2 := hx1 _ hl
    rename_i l
    have hneg : (Vendor.Dyadic.neg l).toReal = - l.toReal := by simp [toReal_def]
    rcases le_total 0 x with h0 | h0
    · rw [abs_of_nonneg h0]; exact le_trans h1 (le_max_toReal_left _ _)
    · rw [abs_of_nonpos h0]
      refine le_trans ?_ (le_max_toReal_right _ _)
      rw [hneg]; linarith

/-! ### Certified comparisons -/

/-- every element of `I` is `<` every element of `J` -/
def ltB (I J : Ival) : Bool :=
  match I.hi, J.lo with
  | some a, some b => Dy.ltB a b
  | _, _ => false

/-- every element of `I` is `≤` every element of `J` -/
def leB (I J : Ival) : Bool :=
  match I.hi, J.lo with
  | some a, some b => Dy.leB a b
  | _, _ => false

theorem lt_of_ltB {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) (h : ltB I J = true) : x < y := by
  unfold ltB at h
  split at h
  · rename_i a b ha hb
    exact lt_of_le_of_lt (hx.2 a ha) (lt_of_lt_of_le (toReal_lt_of_ltB h) (hy.1 b hb))
  · simp at h

theorem le_of_leB {x y : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J) (h : leB I J = true) : x ≤ y := by
  unfold leB at h
  split at h
  · rename_i a b ha hb
    exact le_trans (hx.2 a ha) (le_trans (toReal_le_of_leB h) (hy.1 b hb))
  · simp at h

/-! ### Width, midpoint, bisection -/

/-- upper bound of the width, `none` if infinite -/
def width (I : Ival) : Option Dy := omap2 (fun a b => subU 64 b a) I.lo I.hi

/-- exact midpoint of a finite interval -/
def mid (I : Ival) : Option Dy :=
  omap2 (fun a b => Vendor.Dyadic.scale2 (a.add b) (-1)) I.lo I.hi

/-- bisection at the exact midpoint (finite intervals only; otherwise no split) -/
def bisect (I : Ival) : Ival × Ival :=
  match mid I with
  | some m => (⟨I.lo, some m⟩, ⟨some m, I.hi⟩)
  | none => (I, I)

theorem mem_bisect {x : ℝ} {I : Ival} (hx : x ∈ I) : x ∈ (bisect I).1 ∨ x ∈ (bisect I).2 := by
  unfold bisect
  split
  · rename_i m _
    rcases le_total x m.toReal with h | h
    · exact Or.inl ⟨hx.1, by simpa using h⟩
    · exact Or.inr ⟨by simpa using h, hx.2⟩
  · exact Or.inl hx

/-- lower bound with rounding: `[lo - r, hi + r]` -/
def widen (p : Nat) (I : Ival) (r : Dy) : Ival :=
  ⟨I.lo.map (fun a => subD p a r), I.hi.map (fun b => addU p b r)⟩

theorem mem_widen {p : Nat} {x v : ℝ} {I : Ival} {r : Dy} (hv : v ∈ I) (hxv : |x - v| ≤ r.toReal) :
    x ∈ widen p I r := by
  obtain ⟨hv1, hv2⟩ := hv
  have habs := abs_le.1 hxv
  rcases I with ⟨lo, hi⟩
  refine ⟨?_, ?_⟩
  · cases lo with
    | none => simp [widen]
    | some a =>
      have := hv1 a rfl
      have hs : ((subD p a r).toRat : ℝ) ≤ a.toRat - r.toRat := by exact_mod_cast subD_le p a r
      simp only [widen, Option.map_some, loLe_some]
      simp only [toReal_def] at *; linarith
  · cases hi with
    | none => simp [widen]
    | some b =>
      have := hv2 b rfl
      have hs : (b.toRat : ℝ) + r.toRat ≤ ((addU p b r).toRat : ℝ) := by exact_mod_cast le_addU p b r
      simp only [widen, Option.map_some, leHi_some]
      simp only [toReal_def] at *; linarith

/-- clamp the lower end to be at least `c` (sound when `c ≤ x` is known) -/
def clampLo (I : Ival) (c : Dy) : Ival :=
  ⟨some (match I.lo with | some a => Dy.max a c | none => c), I.hi⟩

theorem mem_clampLo {x : ℝ} {I : Ival} {c : Dy} (hx : x ∈ I) (hc : c.toReal ≤ x) : x ∈ clampLo I c := by
  refine ⟨?_, hx.2⟩
  simp only [clampLo, loLe_some]
  split
  · rename_i a ha
    rcases Dy.toRat_max_eq_or a c with h | h <;> rw [h]
    · exact hx.1 a ha
    · exact hc
  · exact hc

/-- clamp the upper end to be at most `c` (sound when `x ≤ c` is known) -/
def clampHi (I : Ival) (c : Dy) : Ival :=
  ⟨I.lo, some (match I.hi with | some b => Dy.min b c | none => c)⟩

theorem mem_clampHi {x : ℝ} {I : Ival} {c : Dy} (hx : x ∈ I) (hc : x ≤ c.toReal) : x ∈ clampHi I c := by
  refine ⟨hx.1, ?_⟩
  simp only [clampHi, leHi_some]
  split
  · rename_i b hb
    rcases Dy.toRat_min_eq_or b c with h | h <;> rw [h]
    · exact hx.2 b hb
    · exact hc
  · exact hc

/-! ### Square root (monotone; Mathlib `√x = 0` for `x ≤ 0`) -/

def sqrt (p : Nat) (I : Ival) : Ival :=
  ⟨some (match I.lo with | some a => sqrtD p a | none => Dy.zero),
   I.hi.map (fun b => sqrtU p b)⟩

theorem mem_sqrt {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) : Real.sqrt x ∈ sqrt p I := by
  obtain ⟨hx1, hx2⟩ := hx
  rcases I with ⟨lo, hi⟩
  refine ⟨?_, ?_⟩
  · simp only [sqrt, loLe_some]
    cases lo with
    | none => simp [toReal_def, Real.sqrt_nonneg]
    | some a =>
      simp only
      have := hx1 a rfl
      simp only [toReal_def] at this ⊢
      exact le_trans (sqrtD_le p a) (Real.sqrt_le_sqrt this)
  · cases hi with
    | none => simp [sqrt]
    | some b =>
      have hb := hx2 b rfl
      simp only [sqrt, Option.map_some, leHi_some, toReal_def] at hb ⊢
      by_cases hb0 : 0 ≤ b.toRat
      · exact le_trans (Real.sqrt_le_sqrt hb) (le_sqrtU p b hb0)
      · push Not at hb0
        have hx0 : x ≤ 0 := le_trans hb (by exact_mod_cast le_of_lt hb0)
        rw [Real.sqrt_eq_zero'.2 hx0]
        unfold sqrtU
        have : b.mantissa ≤ 0 := by
          have := (toRat_neg_iff b).1 hb0; omega
        simp [this, toRat_zero]

/-! ### Debug printing -/

/-- approximate float value (for traces only) -/
def _root_.Lynth.Interval.Vendor.Dyadic.toFloat (d : Dy) : Float :=
  (Float.ofInt d.mantissa).scaleB d.exponent

/-- human-readable rendering (for traces only) -/
def fmt (I : Ival) : String :=
  let f : Option Dy → String → String := fun o inf => match o with
    | some d => toString d.toFloat
    | none => inf
  s!"[{f I.lo "-inf"}, {f I.hi "+inf"}]"

instance : ToString Ival := ⟨fmt⟩

end Ival

end Lynth.Interval
