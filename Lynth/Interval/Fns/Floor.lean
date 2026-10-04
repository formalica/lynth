import Lynth.Interval.Fns.Elem
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Round

/-!
# Floor, ceiling, rounding

Interval liftings of `Nat.floor`, `Nat.ceil` (`Fn1 .real .nat`, for discrete
witnesses and `ℕ` exponents) and `Int.floor`, `Int.ceil`, `round` folded with
their cast back to `ℝ` (`Fn1 .real .real`, so they nest freely — the cast
cannot be a separate entry since `Ty` has no `int`, exactly like
coq-interval's fused `IZR ∘ Zfloor` node and FLINT's integer-valued balls).

All are monotone endpoint lifts over exact dyadic floors (`Dy.floor` is
`Int` floor division, hence exact); no series, no precision dependence.
See `docs/interval/05-point-goals.md §3`.
-/

namespace Lynth.Interval.Fns

open Lynth.Interval Dy

/-! ### Dyadic floor / ceil / round -/

theorem Dy.floor_le_toRat (d : Dy) : ((Dy.floor d : ℤ) : ℚ) ≤ d.toRat := by
  obtain ⟨m, e⟩ := d
  simp only [Dy.floor]
  split
  · rename_i h
    rw [toRat_mk]
    have e1 : ((m * 2 ^ e.toNat : Int) : ℚ) = (m : ℚ) * (2 : ℚ) ^ e.toNat := by
      push_cast
      ring
    have e2 : (2 : ℚ) ^ e.toNat = (2 : ℚ) ^ e := by
      rw [← zpow_natCast]
      congr 1
      exact Int.toNat_of_nonneg h
    rw [e1, e2]
  · rename_i h
    have he : e < 0 := by omega
    set k := (-e).toNat with hk
    have hkpos : 0 < k := by omega
    have hexp : e = -(k : ℤ) := by omega
    rw [toRat_mk, Int.shiftRight_eq_div_pow]
    have hdiv : (m / (2 ^ k : ℤ)) * (2 ^ k : ℤ) ≤ m :=
      Int.ediv_mul_le _ (ne_of_gt (by positivity))
    have hcast : (((m / (2 ^ k : ℤ) : Int)) : ℚ) * (((2 ^ k : ℤ)) : ℚ) ≤ (m : ℚ) := by
      exact_mod_cast hdiv
    have hpos : (0 : ℚ) < (((2 ^ k : ℤ)) : ℚ) := by positivity
    have eexp : (2 : ℚ) ^ e = ((((2 ^ k : ℤ))) : ℚ)⁻¹ := by
      rw [hexp, zpow_neg]
      congr 1
      rw [zpow_natCast, Int.cast_pow, Int.cast_ofNat]
    rw [eexp, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hcast

theorem Dy.lt_floor_add_one_toRat (d : Dy) :
    d.toRat < ((Dy.floor d : ℤ) : ℚ) + 1 := by
  obtain ⟨m, e⟩ := d
  simp only [Dy.floor]
  split
  · rename_i h
    rw [toRat_mk]
    have e1 : ((m * 2 ^ e.toNat : Int) : ℚ) = (m : ℚ) * (2 : ℚ) ^ e.toNat := by
      push_cast
      ring
    have e2 : (2 : ℚ) ^ e.toNat = (2 : ℚ) ^ e := by
      rw [← zpow_natCast]
      congr 1
      exact Int.toNat_of_nonneg h
    rw [e1, e2]
    simp
  · rename_i h
    have he : e < 0 := by omega
    set k := (-e).toNat with hk
    have hkpos : 0 < k := by omega
    have hexp : e = -(k : ℤ) := by omega
    rw [toRat_mk, Int.shiftRight_eq_div_pow]
    have hdiv : m < (m / (2 ^ k : ℤ) + 1) * (2 ^ k : ℤ) :=
      Int.lt_ediv_add_one_mul_self m (by positivity)
    have hcast : (m : ℚ) < ((((m / (2 ^ k : ℤ) : Int)) : ℚ) + 1) * (((2 ^ k : ℤ)) : ℚ) := by
      exact_mod_cast hdiv
    have hpos : (0 : ℚ) < (((2 ^ k : ℤ)) : ℚ) := by positivity
    have eexp : (2 : ℚ) ^ e = ((((2 ^ k : ℤ))) : ℚ)⁻¹ := by
      rw [hexp, zpow_neg]
      congr 1
      rw [zpow_natCast, Int.cast_pow, Int.cast_ofNat]
    rw [eexp]
    have h2 : (m : ℚ) / ((((2 ^ k : ℤ))) : ℚ)
        < ((((m / (2 ^ k : ℤ) : Int)) : ℚ) + 1) :=
      (div_lt_iff₀ hpos).mpr hcast
    rwa [div_eq_mul_inv] at h2

/-- real floor of a dyadic endpoint. -/
theorem Dy.floor_real (d : Dy) : ⌊d.toReal⌋ = Dy.floor d := by
  rw [Int.floor_eq_iff]
  constructor
  · have h := Dy.floor_le_toRat d
    rw [toReal_def]
    exact_mod_cast h
  · have h := Dy.lt_floor_add_one_toRat d
    rw [toReal_def]
    have h2 : ((((Dy.floor d : ℤ)) : ℚ) + 1 : ℝ) = (((Dy.floor d : ℤ)) : ℝ) + 1 := by
      push_cast
      ring
    rw [← h2]
    exact_mod_cast h

/-- real ceiling via negated floor. -/
def Dy.ceil (d : Dy) : Int := -(Dy.floor (d.neg))

/-- real ceiling of a dyadic endpoint. -/
theorem Dy.ceil_real (d : Dy) : ⌈d.toReal⌉ = Dy.ceil d := by
  rw [Int.ceil_eq_iff, toReal_def]
  have hf : ((Dy.floor (d.neg) : ℤ) : ℚ) ≤ -(d.toRat) := by
    have h := Dy.floor_le_toRat (d.neg)
    simpa [toRat_neg'] using h
  have hl : -(d.toRat) < ((Dy.floor (d.neg) : ℤ) : ℚ) + 1 := by
    have h := Dy.lt_floor_add_one_toRat (d.neg)
    simpa [toRat_neg'] using h
  have e : ((Dy.ceil d : ℤ) : ℝ) = -(((Dy.floor (d.neg) : ℤ)) : ℝ) := by
    simp [Dy.ceil]
  have hfR : (((Dy.floor (d.neg) : ℤ)) : ℝ) ≤ -(((d.toRat : ℚ)) : ℝ) := by
    exact_mod_cast hf
  have hlR : -(((d.toRat : ℚ)) : ℝ) < (((Dy.floor (d.neg) : ℤ)) : ℝ) + 1 := by
    exact_mod_cast hl
  constructor
  · rw [e]; linarith
  · rw [e]; linarith

/-- dyadic half for rounding. -/
def Dy.half : Dy := ⟨1, -1⟩

/-- round a dyadic to `ℤ` (ties up): `⌊d + 1/2⌋`. -/
def Dy.roundInt (d : Dy) : Int := Dy.floor (d.add Dy.half)

theorem Dy.half_toRat : Dy.half.toRat = 1 / 2 := by
  simp [Dy.half, toRat_mk]

/-- real round of a dyadic endpoint. -/
theorem Dy.round_real (d : Dy) : round d.toReal = Dy.roundInt d := by
  rw [round_eq, show d.toReal + 1 / 2 = (d.add Dy.half).toReal from by
    simp [toReal_def, toRat_add', Dy.half_toRat]]
  exact Dy.floor_real _

/-- natural floor of a dyadic endpoint. -/
theorem Dy.floor_nat (d : Dy) : (Dy.floor d).toNat = ⌊d.toReal⌋₊ := by
  rw [← Dy.floor_real d, Int.floor_toNat]

/-- natural ceiling of a dyadic endpoint. -/
theorem Dy.ceil_nat (d : Dy) : (Dy.ceil d).toNat = ⌈d.toReal⌉₊ := by
  rw [← Dy.ceil_real d, Int.ceil_toNat]

/-! ### Generic monotone lifts -/

/-- real-valued monotone endpoint lift (floor, ceil, round). -/
theorem mem_monoIval {F : ℝ → ℝ} {e : Dy → Dy} (hpt : ∀ a, (e a).toReal = F a.toReal)
    (hmono : Monotone F) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    F x ∈ (⟨X.lo.map e, X.hi.map e⟩ : Ival) := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨?_, ?_⟩
  · intro l hl
    cases hlo : X.lo with
    | none => simp [hlo] at hl
    | some a =>
      simp only [hlo, Option.map_some, Option.some.injEq] at hl
      subst hl
      rw [hpt]
      exact hmono (hx1 a hlo)
  · intro h hh
    cases hhi : X.hi with
    | none => simp [hhi] at hh
    | some b =>
      simp only [hhi, Option.map_some, Option.some.injEq] at hh
      subst hh
      rw [hpt]
      exact hmono (hx2 b hhi)

/-- natural-valued monotone lift. -/
theorem mem_monoNIval {F : ℝ → ℕ} {e : Dy → Nat} (hpt : ∀ a, e a = F a.toReal)
    (hmono : Monotone F) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    F x ∈ (⟨match X.lo with | some a => e a | none => 0, X.hi.map e⟩ : NIval) := by
  obtain ⟨hx1, hx2⟩ := hx
  refine ⟨?_, ?_⟩
  · generalize hlo : X.lo = o
    cases o with
    | none => exact Nat.zero_le _
    | some a =>
      show e a ≤ F x
      rw [hpt a]
      exact hmono (hx1 a hlo)
  · intro h hh
    cases hhi : X.hi with
    | none => simp [hhi] at hh
    | some b =>
      simp only [hhi, Option.map_some, Option.some.injEq] at hh
      subst hh
      rw [hpt]
      exact hmono (hx2 b hhi)

/-! ### Entries -/

/-- `⌊·⌋₊`, exact on endpoints. -/
def natFloorIval (X : Ival) : NIval :=
  ⟨match X.lo with | some a => (Dy.floor a).toNat | none => 0,
   X.hi.map (fun b => (Dy.floor b).toNat)⟩

theorem mem_natFloor {x : ℝ} {X : Ival} (hx : x ∈ X) : ⌊x⌋₊ ∈ natFloorIval X := by
  unfold natFloorIval
  exact mem_monoNIval (fun a => Dy.floor_nat a) Nat.floor_mono hx

@[lynth_fn] def natFloorR : Fn1 .real .nat where
  name := "⌊·⌋₊"
  graph x n := n = ⌊x⌋₊
  exu := exu_eq _
  ev _ := natFloorIval
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact mem_natFloor hx
  cost := 5

/-- `⌈·⌉₊`, exact on endpoints. -/
def natCeilIval (X : Ival) : NIval :=
  ⟨match X.lo with | some a => (Dy.ceil a).toNat | none => 0,
   X.hi.map (fun b => (Dy.ceil b).toNat)⟩

theorem mem_natCeil {x : ℝ} {X : Ival} (hx : x ∈ X) : ⌈x⌉₊ ∈ natCeilIval X := by
  unfold natCeilIval
  exact mem_monoNIval (fun a => Dy.ceil_nat a) Nat.ceil_mono hx

@[lynth_fn] def natCeilR : Fn1 .real .nat where
  name := "⌈·⌉₊"
  graph x n := n = ⌈x⌉₊
  exu := exu_eq _
  ev _ := natCeilIval
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact mem_natCeil hx
  cost := 5

/-- `↑⌊·⌋`, real-valued for free nesting. -/
def intFloorIval (X : Ival) : Ival :=
  ⟨X.lo.map (fun a => Dy.ofInt (Dy.floor a)), X.hi.map (fun b => Dy.ofInt (Dy.floor b))⟩

theorem mem_intFloor {x : ℝ} {X : Ival} (hx : x ∈ X) :
    ((⌊x⌋ : ℤ) : ℝ) ∈ intFloorIval X := by
  unfold intFloorIval
  have hpt : ∀ a : Dy, ((Dy.ofInt (Dy.floor a)).toReal) = ((⌊a.toReal⌋ : ℤ) : ℝ) := by
    intro a
    have e : ((Dy.ofInt (Dy.floor a)).toReal) = ((Dy.floor a : ℤ) : ℝ) := by
      simp [toReal_def, toRat_ofInt, Rat.cast_intCast]
    rw [e, ← Dy.floor_real a]
  have hmono : Monotone (fun x : ℝ => ((⌊x⌋ : ℤ) : ℝ)) := by
    intro a b h
    show ((⌊a⌋ : ℤ) : ℝ) ≤ ((⌊b⌋ : ℤ) : ℝ)
    exact_mod_cast Int.floor_mono h
  exact mem_monoIval hpt hmono hx

@[lynth_fn] def intFloorR : Fn1 .real .real where
  name := "⌊·⌋"
  graph x y := y = ((⌊x⌋ : ℤ) : ℝ)
  exu := exu_eq _
  ev _ := intFloorIval
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact mem_intFloor hx
  cost := 10

/-- `↑⌈·⌉`, real-valued for free nesting. -/
def intCeilIval (X : Ival) : Ival :=
  ⟨X.lo.map (fun a => Dy.ofInt (Dy.ceil a)), X.hi.map (fun b => Dy.ofInt (Dy.ceil b))⟩

theorem mem_intCeil {x : ℝ} {X : Ival} (hx : x ∈ X) :
    ((⌈x⌉ : ℤ) : ℝ) ∈ intCeilIval X := by
  unfold intCeilIval
  have hpt : ∀ a : Dy, ((Dy.ofInt (Dy.ceil a)).toReal) = ((⌈a.toReal⌉ : ℤ) : ℝ) := by
    intro a
    have e : ((Dy.ofInt (Dy.ceil a)).toReal) = ((Dy.ceil a : ℤ) : ℝ) := by
      simp [toReal_def, toRat_ofInt, Rat.cast_intCast]
    rw [e, ← Dy.ceil_real a]
  have hmono : Monotone (fun x : ℝ => ((⌈x⌉ : ℤ) : ℝ)) := by
    intro a b h
    show ((⌈a⌉ : ℤ) : ℝ) ≤ ((⌈b⌉ : ℤ) : ℝ)
    exact_mod_cast Int.ceil_mono h
  exact mem_monoIval hpt hmono hx

@[lynth_fn] def intCeilR : Fn1 .real .real where
  name := "⌈·⌉"
  graph x y := y = ((⌈x⌉ : ℤ) : ℝ)
  exu := exu_eq _
  ev _ := intCeilIval
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact mem_intCeil hx
  cost := 10

/-- `↑round(·)`, real-valued for free nesting. -/
def intRoundIval (X : Ival) : Ival :=
  ⟨X.lo.map (fun a => Dy.ofInt (Dy.roundInt a)), X.hi.map (fun b => Dy.ofInt (Dy.roundInt b))⟩

theorem round_mono' : Monotone (fun x : ℝ => ((round x : ℤ) : ℝ)) := by
  intro a b h
  have e : ∀ x : ℝ, round x = ⌊x + 1 / 2⌋ := round_eq
  show ((round a : ℤ) : ℝ) ≤ ((round b : ℤ) : ℝ)
  rw [e, e]
  exact_mod_cast Int.floor_mono (by linarith)

theorem mem_intRound {x : ℝ} {X : Ival} (hx : x ∈ X) :
    ((round x : ℤ) : ℝ) ∈ intRoundIval X := by
  unfold intRoundIval
  have hpt : ∀ a : Dy, ((Dy.ofInt (Dy.roundInt a)).toReal) = ((round a.toReal : ℤ) : ℝ) := by
    intro a
    have e : ((Dy.ofInt (Dy.roundInt a)).toReal) = ((Dy.roundInt a : ℤ) : ℝ) := by
      simp [toReal_def, toRat_ofInt, Rat.cast_intCast]
    rw [e, ← Dy.round_real a]
  exact mem_monoIval hpt round_mono' hx

@[lynth_fn] def intRoundR : Fn1 .real .real where
  name := "round"
  graph x y := y = ((round x : ℤ) : ℝ)
  exu := exu_eq _
  ev _ := intRoundIval
  sound := fun _ _ _ _ _ hy hx => by obtain rfl := hy; exact mem_intRound hx
  cost := 10

end Lynth.Interval.Fns
