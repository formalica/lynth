import Lynth.Interval.Core.Asy
import Mathlib.Data.Nat.Fib.Basic

/-!
# AIA operations with soundness

Rules of `docs/interval/08-series.md §2`.  All constants are computed with
rational/dyadic arithmetic only (no transcendental kernels): a real power
`x^α` of a rational `x > 0` is enclosed between `x^⌊α⌋` and `x^⌈α⌉`.
-/

namespace Lynth.Interval

open Dy

/-! ### Helpers -/

theorem Ival.mem_hull_of_between {x y v : ℝ} {I J : Ival} (hx : x ∈ I) (hy : y ∈ J)
    (h1 : Min.min x y ≤ v) (h2 : v ≤ Max.max x y) : v ∈ Ival.hull I J := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  refine ⟨Ival.loLe_omap2 ?_, Ival.leHi_omap2 ?_⟩
  · intro u w hu hw
    exact le_trans (le_min (le_trans (Ival.min_toReal_le_left u w) (hx1 u hu))
      (le_trans (Ival.min_toReal_le_right u w) (hy1 w hw))) h1
  · intro u w hu hw
    exact le_trans h2 (max_le (le_trans (hx2 u hu) (Ival.le_max_toReal_left u w))
      (le_trans (hy2 w hw) (Ival.le_max_toReal_right u w)))

/-- `x^α` lies between `x^⌊α⌋` and `x^⌈α⌉` (`x > 0`) -/
theorem rpow_between_floor_ceil {x : ℝ} (hx : 0 < x) (α : ℚ) :
    Min.min (x ^ ((⌊α⌋ : ℤ) : ℝ)) (x ^ ((⌈α⌉ : ℤ) : ℝ)) ≤ x ^ (α : ℝ) ∧
      x ^ (α : ℝ) ≤ Max.max (x ^ ((⌊α⌋ : ℤ) : ℝ)) (x ^ ((⌈α⌉ : ℤ) : ℝ)) := by
  have hf : ((⌊α⌋ : ℤ) : ℝ) ≤ (α : ℝ) := by exact_mod_cast Int.floor_le α
  have hc : (α : ℝ) ≤ ((⌈α⌉ : ℤ) : ℝ) := by exact_mod_cast Int.le_ceil α
  rcases le_total 1 x with h1 | h1
  · have a := Real.rpow_le_rpow_of_exponent_le h1 hf
    have b := Real.rpow_le_rpow_of_exponent_le h1 hc
    exact ⟨le_trans (min_le_left _ _) a, le_trans b (le_max_right _ _)⟩
  · have a := Real.rpow_le_rpow_of_exponent_ge hx h1 hf
    have b := Real.rpow_le_rpow_of_exponent_ge hx h1 hc
    exact ⟨le_trans (min_le_right _ _) b, le_trans a (le_max_left _ _)⟩

/-- enclosure of `x^α` (`x > 0` rational, `α` rational) via integer powers -/
def qpowEncl (p : Nat) (x α : ℚ) : Ival :=
  Ival.hull (Ival.ofRat p (x ^ ⌊α⌋)) (Ival.ofRat p (x ^ ⌈α⌉))

theorem mem_qpowEncl (p : Nat) {x : ℚ} (hx : 0 < x) (α : ℚ) :
    ((x : ℝ)) ^ (α : ℝ) ∈ qpowEncl p x α := by
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  obtain ⟨h1, h2⟩ := rpow_between_floor_ceil hx' α
  have e1 : ((x ^ ⌊α⌋ : ℚ) : ℝ) = (x : ℝ) ^ ((⌊α⌋ : ℤ) : ℝ) := by
    rw [Real.rpow_intCast]; push_cast; rfl
  have e2 : ((x ^ ⌈α⌉ : ℚ) : ℝ) = (x : ℝ) ^ ((⌈α⌉ : ℤ) : ℝ) := by
    rw [Real.rpow_intCast]; push_cast; rfl
  refine Ival.mem_hull_of_between (Ival.mem_ofRat p _) (Ival.mem_ofRat p _) ?_ ?_
  · rw [e1, e2]; exact h1
  · rw [e1, e2]; exact h2

/-- `[0, hi X]` -/
def Ival.zeroTo (X : Ival) : Ival := ⟨some Dy.zero, X.hi⟩

theorem Ival.mem_zeroTo {x : ℝ} {X : Ival} (h0 : 0 ≤ x) (hx : x ∈ X) : x ∈ Ival.zeroTo X :=
  ⟨fun l hl => by cases hl; simpa [toReal_def] using h0, hx.2⟩

/-- the point value of a degenerate interval -/
def Ival.point? (I : Ival) : Option Dy :=
  match I.lo, I.hi with
  | some a, some b => if Dy.leB b a then some a else none
  | _, _ => none

theorem Ival.eq_of_point? {I : Ival} {x : ℝ} {d : Dy} (hx : x ∈ I) (h : I.point? = some d) :
    x = d.toReal := by
  unfold Ival.point? at h
  cases hl : I.lo with
  | none => simp [hl] at h
  | some a =>
    cases hh : I.hi with
    | none => simp [hl, hh] at h
    | some b =>
      simp only [hl, hh] at h
      split at h
      · rename_i hba
        cases h
        have h1 := hx.1 d hl; have h2 := hx.2 b hh
        have := toReal_le_of_leB hba
        linarith
      · cases h

/-! ### Negation, rebasing -/

namespace RAsy

theorem holds_congr {N : ℕ} {f g : ℕ → ℝ} {A : RAsy} (h : A.Holds N f)
    (he : ∀ k, N ≤ k → f k = g k) : A.Holds N g := by
  cases A with
  | pow a α I J =>
    intro k hk
    obtain ⟨hpos, u, hu, hJ, hfe⟩ := h k hk
    exact ⟨hpos, u, hu, hJ, by rw [← he k hk]; exact hfe⟩
  | geo M R => intro k hk; rw [← he k hk]; exact h k hk
  | grow M R => intro k hk; rw [← he k hk]; exact h k hk
  | top => trivial

def neg : RAsy → RAsy
  | pow a α I J => pow a α (Ival.neg I) J
  | geo M R => geo M R
  | _ => top

theorem neg_holds {N : ℕ} {f : ℕ → ℝ} {A : RAsy} (h : A.Holds N f) :
    (neg A).Holds N (fun k => -f k) := by
  cases A with
  | pow a α I J =>
    intro k hk
    obtain ⟨hpos, u, hu, hJ, he⟩ := h k hk
    exact ⟨hpos, -u, Ival.mem_neg hu, by rwa [abs_neg], by show -f k = _; rw [he]; ring⟩
  | geo M R => intro k hk; rw [abs_neg]; exact h k hk
  | grow => trivial
  | top => trivial

/-- `Q ∋ ((k + a) / (k + a'))^α` for all `k ≥ N` -/
def rebaseQ (p N a a' : ℕ) (α : ℚ) : Ival :=
  Ival.hull Ival.one (qpowEncl p (((N + a : ℕ) : ℚ) / ((N + a' : ℕ) : ℚ)) α)

theorem mem_rebaseQ (p : ℕ) {N a a' k : ℕ} (hk : N ≤ k) (hN : 0 < N + a') (hNa : 0 < N + a)
    (α : ℚ) : (((k : ℝ) + a) / ((k : ℝ) + a')) ^ (α : ℝ) ∈ rebaseQ p N a a' α := by
  set r : ℚ := ((N + a : ℕ) : ℚ) / ((N + a' : ℕ) : ℚ)
  have hr : 0 < r := by positivity
  have hmem := mem_qpowEncl p hr α
  have hr' : ((r : ℚ) : ℝ) = ((N : ℝ) + a) / ((N : ℝ) + a') := by
    simp [r]
  rw [hr'] at hmem
  have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
  have hN' : (0 : ℝ) < N + a' := by exact_mod_cast hN
  have hNa' : (0 : ℝ) < N + a := by exact_mod_cast hNa
  have hka : (0 : ℝ) < k + a := by linarith
  have hka' : (0 : ℝ) < k + a' := by linarith
  set t : ℝ := ((k : ℝ) + a) / ((k : ℝ) + a')
  set r0 : ℝ := ((N : ℝ) + a) / ((N : ℝ) + a')
  have ht : 0 < t := div_pos hka hka'
  have hr0 : 0 < r0 := div_pos hNa' hN'
  -- `t` lies between `r0` and `1`
  have hbetween : (r0 ≤ t ∧ t ≤ 1) ∨ (1 ≤ t ∧ t ≤ r0) := by
    rcases le_total a a' with h | h
    · left
      have h' : (a : ℝ) ≤ a' := by exact_mod_cast h
      constructor
      · rw [div_le_div_iff₀ hN' hka']; nlinarith
      · rw [div_le_one hka']; linarith
    · right
      have h' : (a' : ℝ) ≤ a := by exact_mod_cast h
      constructor
      · rw [one_le_div hka']; linarith
      · rw [div_le_div_iff₀ hka' hN']; nlinarith
  have h1 : (1 : ℝ) ∈ Ival.one := Ival.mem_one
  refine Ival.mem_hull_of_between h1 hmem ?_ ?_
  · rcases le_total 0 (α : ℝ) with hα | hα <;> rcases hbetween with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow hr0.le b1 hα)
    · exact le_trans (min_le_left _ _) (by simpa using Real.rpow_le_rpow zero_le_one b1 hα)
    · exact le_trans (min_le_left _ _) (by simpa using Real.rpow_le_rpow_of_nonpos ht b2 hα)
    · exact le_trans (min_le_right _ _) (Real.rpow_le_rpow_of_nonpos ht b2 hα)
  · rcases le_total 0 (α : ℝ) with hα | hα <;> rcases hbetween with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · exact le_trans (by simpa using Real.rpow_le_rpow ht.le b2 hα) (le_max_left _ _)
    · exact le_trans (Real.rpow_le_rpow ht.le b2 hα) (le_max_right _ _)
    · exact le_trans (Real.rpow_le_rpow_of_nonpos hr0 b1 hα) (le_max_right _ _)
    · exact le_trans (by simpa using Real.rpow_le_rpow_of_nonpos zero_lt_one b1 hα) (le_max_left _ _)

/-- change the base shift of a `pow` value to `a'` -/
def rebase (p N a' : ℕ) : RAsy → RAsy
  | pow a α I J =>
    if a = a' then pow a α I J
    else if N + a' = 0 then top
    else if N + a = 0 then top
    else
      let Q := rebaseQ p N a a' α
      pow a' α (Ival.mul p I Q) (Ival.mul p J Q)
  | _ => top

theorem rebase_holds {p N a' : ℕ} {f : ℕ → ℝ} {A : RAsy} (h : A.Holds N f) :
    (rebase p N a' A).Holds N f := by
  cases A with
  | pow a α I J =>
    show Holds N f (if a = a' then pow a α I J else if N + a' = 0 then top
      else if N + a = 0 then top else pow a' α (Ival.mul p I (rebaseQ p N a a' α))
        (Ival.mul p J (rebaseQ p N a a' α)))
    split_ifs with h0 h1 h2
    · exact h
    · trivial
    · trivial
    intro k hk
    obtain ⟨hpos, u, hu, hJ, he⟩ := h k hk
    have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    have hN1 : (0 : ℝ) < N + a' := by exact_mod_cast Nat.pos_of_ne_zero h1
    have hka' : (0 : ℝ) < k + a' := by linarith
    have hQ := mem_rebaseQ p hk (Nat.pos_of_ne_zero h1) (Nat.pos_of_ne_zero h2) α
    set q := (((k : ℝ) + a) / ((k : ℝ) + a')) ^ (α : ℝ)
    have hq0 : 0 ≤ q := Real.rpow_nonneg (div_nonneg hpos.le hka'.le) _
    refine ⟨hka', u * q, Ival.mem_mul hu hQ, ?_, ?_⟩
    · rw [abs_mul, abs_of_nonneg hq0]; exact Ival.mem_mul hJ hQ
    · rw [he]
      have : ((k : ℝ) + a) = ((k : ℝ) + a) / ((k : ℝ) + a') * ((k : ℝ) + a') := by
        field_simp
      rw [this, Real.mul_rpow (div_nonneg hpos.le hka'.le) hka'.le]
      ring
  | geo => trivial
  | grow => trivial
  | top => trivial

end RAsy

/-! ### Real-valued rounding facts -/

theorem Dy.addD_toReal (p : ℕ) (a b : Dy) : (addD p a b).toReal ≤ a.toReal + b.toReal := by
  simp only [toReal_def]; exact_mod_cast addD_le p a b
theorem Dy.le_addU_toReal (p : ℕ) (a b : Dy) : a.toReal + b.toReal ≤ (addU p a b).toReal := by
  simp only [toReal_def]; exact_mod_cast le_addU p a b
theorem Dy.mulD_toReal (p : ℕ) (a b : Dy) : (mulD p a b).toReal ≤ a.toReal * b.toReal := by
  simp only [toReal_def]; exact_mod_cast mulD_le p a b
theorem Dy.le_mulU_toReal (p : ℕ) (a b : Dy) : a.toReal * b.toReal ≤ (mulU p a b).toReal := by
  simp only [toReal_def]; exact_mod_cast le_mulU p a b
theorem Dy.nonneg_of_isNonneg {a : Dy} (h : isNonneg a = true) : 0 ≤ a.toReal := by
  simp only [toReal_def]; exact_mod_cast (isNonneg_iff a).1 h
theorem Dy.pos_of_isPos {a : Dy} (h : isPos a = true) : 0 < a.toReal := by
  simp only [toReal_def]; exact_mod_cast (isPos_iff a).1 h
theorem Dy.one_le_of_leB {a : Dy} (h : leB Dy.one a = true) : 1 ≤ a.toReal := by
  have := toReal_le_of_leB h; simpa [toReal_def] using this
theorem Dy.lt_of_ltB' {a b : Dy} (h : ltB a b = true) : a.toReal < b.toReal := toReal_lt_of_ltB h
theorem Dy.one_div_le_divU (p : ℕ) {a : Dy} (ha : 0 < a.toReal) :
    1 / a.toReal ≤ (divU p Dy.one a).toReal := by
  have h := le_divU p Dy.one a (by
    intro h0; have : a.toReal = 0 := by simp [toReal_def, h0]
    linarith)
  simp only [toRat_one] at h
  simp only [toReal_def]; exact_mod_cast h

/-- the exact natural-number value of a dyadic, if any -/
def Dy.natOf? (d : Dy) : Option ℕ :=
  let q := d.toRat
  if q.den = 1 ∧ 0 ≤ q.num then some q.num.toNat else none

theorem Dy.natOf?_spec {d : Dy} {n : ℕ} (h : d.natOf? = some n) : d.toReal = n := by
  unfold Dy.natOf? at h
  simp only at h
  split_ifs at h with hq
  cases h
  obtain ⟨h1, h2⟩ := hq
  have e1 : ((d.toRat.num.toNat : ℕ) : ℚ) = d.toRat := by
    rw [show ((d.toRat.num.toNat : ℕ) : ℚ) = ((d.toRat.num.toNat : ℤ) : ℚ) by push_cast; rfl,
      Int.toNat_of_nonneg h2]
    exact Rat.coe_int_num_of_den_eq_one h1
  simp only [toReal_def]; rw [← e1]; push_cast; rfl

theorem Ival.mem_zeroTo' {x : ℝ} {X : Ival} (h0 : 0 ≤ x) (hle : ∀ h, X.hi = some h → x ≤ h.toReal) :
    x ∈ Ival.zeroTo X :=
  ⟨fun l hl => by cases hl; simpa [toReal_def] using h0, hle⟩

namespace RAsy

/-! ### Addition -/

/-- `(k + a) + c` with `c` a natural-number constant: exact shift -/
def shiftConst? (a : ℕ) (α : ℚ) (I : Ival) (β : ℚ) (K : Ival) : Option ℕ :=
  if α = 1 ∧ β = 0 then
    match I.point?, K.point? with
    | some u, some v => if Dy.leB u Dy.one && Dy.leB Dy.one u then (v.natOf?).map (a + ·) else none
    | _, _ => none
  else none

def addPow (p N a : ℕ) (α : ℚ) (I : Ival) (b : ℕ) (β : ℚ) (K L : Ival) : RAsy :=
  match shiftConst? a α I β K with
  | some a' => pow a' 1 Ival.one Ival.one
  | none =>
    match rebase p N a (pow b β K L) with
    | pow a₀ β' K' _ =>
      if a₀ = a then
        if α = β' then
          let S := Ival.add p I K'
          pow a α S (Ival.abs S)
        else if β' < α then
          let S := Ival.add p I (Ival.mul p K' (Ival.zeroTo (qpowEncl p ((N + a : ℕ) : ℚ) (β' - α))))
          pow a α S (Ival.abs S)
        else
          let S := Ival.add p (Ival.mul p I (Ival.zeroTo (qpowEncl p ((N + a : ℕ) : ℚ) (α - β')))) K'
          pow a β' S (Ival.abs S)
      else top
    | _ => top

/-- `grow + (bounded)`: `M R^j + v ≥ (M + min(lo, 0)) R^j` for `R ≥ 1` -/
def growAddConst (p : ℕ) (M R : Dy) (K : Ival) : RAsy :=
  if Dy.leB Dy.one R then
    match K.lo with
    | some l => grow (addD p M (Dy.min l Dy.zero)) R
    | none => top
  else top

def isTop : RAsy → Bool
  | top => true
  | _ => false

def add (p N : ℕ) : RAsy → RAsy → RAsy
  | pow a α I J, pow b β K L =>
    let r := addPow p N a α I b β K L
    if r.isTop then addPow p N b β K a α I J else r
  | geo M R, geo M' R' =>
    if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' then geo (addU p M M') (Dy.max R R')
    else top
  | grow M R, pow _ β K _ => if β = 0 then growAddConst p M R K else top
  | pow _ β K _, grow M R => if β = 0 then growAddConst p M R K else top
  | _, _ => top

theorem addPow_holds {p N a : ℕ} {α : ℚ} {I J : Ival} {b : ℕ} {β : ℚ} {K L : Ival} {f g : ℕ → ℝ}
    (hf : (pow a α I J).Holds N f) (hg : (pow b β K L).Holds N g) :
    (addPow p N a α I b β K L).Holds N (fun k => f k + g k) := by
  unfold addPow
  split
  · -- exact shift
    rename_i a' hs
    unfold shiftConst? at hs
    split at hs
    · rename_i hαβ
      obtain ⟨hα, hβ⟩ := hαβ
      split at hs
      · rename_i u v hu hv
        split at hs
        · rename_i hu1
          simp only [Bool.and_eq_true] at hu1
          obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.1 hs
          intro k hk
          obtain ⟨hpos, x, hx, _, hfe⟩ := hf k hk
          obtain ⟨_, y, hy, _, hge⟩ := hg k hk
          have hx1 : x = u.toReal := Ival.eq_of_point? hx hu
          have hu' : u.toReal = 1 := le_antisymm (by simpa [toReal_def] using toReal_le_of_leB hu1.1)
            (by simpa [toReal_def] using toReal_le_of_leB hu1.2)
          have hy1 : y = v.toReal := Ival.eq_of_point? hy hv
          have hvn := Dy.natOf?_spec hn
          subst hα; subst hβ
          have hkn : (0 : ℝ) < (k : ℝ) + ((a + n : ℕ) : ℝ) := by
            push_cast; linarith [hpos, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
          refine ⟨hkn, 1, Ival.mem_one, by simpa using Ival.mem_one, ?_⟩
          show f k + g k = _
          rw [hfe, hge, hx1, hu', hy1, hvn]
          push_cast
          simp [Real.rpow_one]
          ring
        · cases hs
      · cases hs
    · cases hs
  · rename_i hnone
    have hr := rebase_holds (p := p) (a' := a) hg
    split
    · rename_i a₀ β' K' L' heq
      rw [heq] at hr
      split
      · rename_i ha₀
        subst ha₀
        split
        · -- same exponent
          rename_i hαβ
          subst hαβ
          intro k hk
          obtain ⟨hpos, x, hx, _, hfe⟩ := hf k hk
          obtain ⟨_, y, hy, _, hge⟩ := hr k hk
          refine ⟨hpos, x + y, Ival.mem_add hx hy, Ival.mem_abs (Ival.mem_add hx hy), ?_⟩
          show f k + g k = _
          rw [hfe, hge]; ring
        split
        · -- β' < α
          rename_i _ hlt
          intro k hk
          obtain ⟨hpos, x, hx, _, hfe⟩ := hf k hk
          obtain ⟨_, y, hy, _, hge⟩ := hr k hk
          have hNpos : (0 : ℝ) < (N : ℝ) + a₀ := (hf N le_rfl).1
          have hNq : (0 : ℚ) < ((N + a₀ : ℕ) : ℚ) := by
            have : (0 : ℝ) < ((N + a₀ : ℕ) : ℝ) := by push_cast; exact hNpos
            exact_mod_cast this
          set e : ℝ := ((k : ℝ) + a₀) ^ ((β' - α : ℚ) : ℝ)
          have he0 : 0 ≤ e := Real.rpow_nonneg hpos.le _
          have hmem : e ∈ Ival.zeroTo (qpowEncl p ((N + a₀ : ℕ) : ℚ) (β' - α)) := by
            refine Ival.mem_zeroTo' he0 (fun h hh => ?_)
            have hq := (mem_qpowEncl p hNq (β' - α)).2 h hh
            have hc : (((N + a₀ : ℕ) : ℚ) : ℝ) = (N : ℝ) + a₀ := by push_cast; ring
            rw [hc] at hq
            refine le_trans ?_ hq
            have hk' : (N : ℝ) + a₀ ≤ (k : ℝ) + a₀ := by
              have : (N : ℝ) ≤ k := by exact_mod_cast hk
              linarith
            have hneg : ((β' - α : ℚ) : ℝ) ≤ 0 := by
              have : β' - α ≤ 0 := by linarith
              exact_mod_cast this
            exact Real.rpow_le_rpow_of_nonpos hNpos hk' hneg
          refine ⟨hpos, x + y * e, Ival.mem_add hx (Ival.mem_mul hy hmem),
            Ival.mem_abs (Ival.mem_add hx (Ival.mem_mul hy hmem)), ?_⟩
          show f k + g k = _
          rw [hfe, hge]
          have : ((k : ℝ) + a₀) ^ (β' : ℝ) = ((k : ℝ) + a₀) ^ (α : ℝ) * e := by
            rw [← Real.rpow_add hpos]; congr 1; push_cast; ring
          rw [this]; ring
        · -- α < β'
          rename_i hne hnlt
          have hlt : α < β' := lt_of_le_of_ne (not_lt.1 hnlt) hne
          intro k hk
          obtain ⟨hpos, x, hx, _, hfe⟩ := hf k hk
          obtain ⟨_, y, hy, _, hge⟩ := hr k hk
          have hNpos : (0 : ℝ) < (N : ℝ) + a₀ := (hf N le_rfl).1
          have hNq : (0 : ℚ) < ((N + a₀ : ℕ) : ℚ) := by
            have : (0 : ℝ) < ((N + a₀ : ℕ) : ℝ) := by push_cast; exact hNpos
            exact_mod_cast this
          set e : ℝ := ((k : ℝ) + a₀) ^ ((α - β' : ℚ) : ℝ)
          have he0 : 0 ≤ e := Real.rpow_nonneg hpos.le _
          have hmem : e ∈ Ival.zeroTo (qpowEncl p ((N + a₀ : ℕ) : ℚ) (α - β')) := by
            refine Ival.mem_zeroTo' he0 (fun h hh => ?_)
            have hq := (mem_qpowEncl p hNq (α - β')).2 h hh
            have hc : (((N + a₀ : ℕ) : ℚ) : ℝ) = (N : ℝ) + a₀ := by push_cast; ring
            rw [hc] at hq
            refine le_trans ?_ hq
            have hk' : (N : ℝ) + a₀ ≤ (k : ℝ) + a₀ := by
              have : (N : ℝ) ≤ k := by exact_mod_cast hk
              linarith
            have hneg : ((α - β' : ℚ) : ℝ) ≤ 0 := by
              have : α - β' ≤ 0 := by linarith
              exact_mod_cast this
            exact Real.rpow_le_rpow_of_nonpos hNpos hk' hneg
          refine ⟨hpos, x * e + y, Ival.mem_add (Ival.mem_mul hx hmem) hy,
            Ival.mem_abs (Ival.mem_add (Ival.mem_mul hx hmem) hy), ?_⟩
          show f k + g k = _
          rw [hfe, hge]
          have : ((k : ℝ) + a₀) ^ (α : ℝ) = ((k : ℝ) + a₀) ^ (β' : ℝ) * e := by
            rw [← Real.rpow_add hpos]; congr 1; push_cast; ring
          rw [this]; ring
      · trivial
    · trivial

theorem growAddConst_holds {p N : ℕ} {M R : Dy} {b : ℕ} {K L : Ival} {f g : ℕ → ℝ}
    (hf : (grow M R).Holds N f) (hg : (pow b 0 K L).Holds N g) :
    (growAddConst p M R K).Holds N (fun k => f k + g k) := by
  unfold growAddConst
  split
  · rename_i hR
    have hR1 := Dy.one_le_of_leB hR
    split
    · rename_i l hl
      intro k hk
      have h1 := hf k hk
      obtain ⟨_, v, hv, _, hge⟩ := hg k hk
      have hgv : g k = v := by rw [hge]; simp
      have hlv : l.toReal ≤ v := hv.1 l hl
      have hm1 := Ival.min_toReal_le_left l Dy.zero
      have hm0 : (Dy.min l Dy.zero).toReal ≤ 0 := by
        have := Ival.min_toReal_le_right l Dy.zero; simpa [toReal_def] using this
      have hRj : 1 ≤ R.toReal ^ (k - N) := one_le_pow₀ hR1
      have hadd := Dy.addD_toReal p M (Dy.min l Dy.zero)
      show (addD p M (Dy.min l Dy.zero)).toReal * R.toReal ^ (k - N) ≤ f k + g k
      rw [hgv]
      nlinarith
    · trivial
  · trivial

theorem add_holds {p N : ℕ} {f g : ℕ → ℝ} {A B : RAsy} (hf : A.Holds N f) (hg : B.Holds N g) :
    (add p N A B).Holds N (fun k => f k + g k) := by
  cases A with
  | pow a α I J =>
    cases B with
    | pow b β K L =>
      show (if (addPow p N a α I b β K L).isTop then addPow p N b β K a α I J
        else addPow p N a α I b β K L).Holds N _
      split
      · have e : (fun k => f k + g k) = (fun k => g k + f k) := funext fun k => add_comm _ _
        rw [e]; exact addPow_holds hg hf
      · exact addPow_holds hf hg
    | grow M R =>
      show (if α = 0 then growAddConst p M R I else top).Holds N _
      split
      · rename_i hα; subst hα
        have e : (fun k => f k + g k) = (fun k => g k + f k) := funext fun k => add_comm _ _
        rw [e]; exact growAddConst_holds hg hf
      · trivial
    | geo => trivial
    | top => trivial
  | geo M R =>
    cases B with
    | geo M' R' =>
      show (if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' then
        geo (addU p M M') (Dy.max R R') else top).Holds N _
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨hM, hM'⟩, hR⟩, hR'⟩ := h
        have hM0 := Dy.nonneg_of_isNonneg hM; have hM0' := Dy.nonneg_of_isNonneg hM'
        have hR0 := Dy.nonneg_of_isNonneg hR; have hR0' := Dy.nonneg_of_isNonneg hR'
        intro k hk
        have h1 := hf k hk; have h2 := hg k hk
        have hm1 : R.toReal ^ (k - N) ≤ (Dy.max R R').toReal ^ (k - N) :=
          pow_le_pow_left₀ hR0 (Ival.le_max_toReal_left R R') _
        have hm2 : R'.toReal ^ (k - N) ≤ (Dy.max R R').toReal ^ (k - N) :=
          pow_le_pow_left₀ hR0' (Ival.le_max_toReal_right R R') _
        have hu := Dy.le_addU_toReal p M M'
        have hmx : 0 ≤ (Dy.max R R').toReal ^ (k - N) :=
          pow_nonneg (le_trans hR0 (Ival.le_max_toReal_left R R')) _
        show |f k + g k| ≤ _
        calc |f k + g k| ≤ |f k| + |g k| := abs_add_le _ _
          _ ≤ M.toReal * (Dy.max R R').toReal ^ (k - N) + M'.toReal * (Dy.max R R').toReal ^ (k - N) := by
            nlinarith
          _ ≤ _ := by nlinarith
      · trivial
    | _ => trivial
  | grow M R =>
    cases B with
    | pow b β K L =>
      show (if β = 0 then growAddConst p M R K else top).Holds N _
      split
      · rename_i hβ; subst hβ; exact growAddConst_holds hf hg
      · trivial
    | _ => trivial
  | top => trivial

/-! ### Multiplication -/

def mulPowGeo (p N a : ℕ) (α : ℚ) (J : Ival) (M R : Dy) : RAsy :=
  if α ≤ 0 ∧ 0 < N + a ∧ isNonneg R = true then
    match J.hi, (qpowEncl p ((N + a : ℕ) : ℚ) α).hi with
    | some jh, some e => geo (mulU p (mulU p M e) jh) R
    | _, _ => top
  else top

def growMulConst (p : ℕ) (M R : Dy) (K : Ival) : RAsy :=
  if isNonneg M && isNonneg R then
    match K.lo with
    | some l => if isNonneg l then grow (mulD p M l) R else top
    | none => top
  else top

def mul (p N : ℕ) : RAsy → RAsy → RAsy
  | pow a α I J, pow b β K L =>
    match rebase p N a (pow b β K L) with
    | pow a₀ β' K' L' => if a₀ = a then pow a (α + β') (Ival.mul p I K') (Ival.mul p J L') else top
    | _ => top
  | pow a α _ J, geo M R => mulPowGeo p N a α J M R
  | geo M R, pow a α _ J => mulPowGeo p N a α J M R
  | geo M R, geo M' R' =>
    if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' then geo (mulU p M M') (mulU p R R')
    else top
  | grow M R, grow M' R' =>
    if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' && isNonneg (mulD p R R') then
      grow (mulD p M M') (mulD p R R')
    else top
  | grow M R, pow _ β K _ => if β = 0 then growMulConst p M R K else top
  | pow _ β K _, grow M R => if β = 0 then growMulConst p M R K else top
  | _, _ => top

theorem mulPowGeo_holds {p N a : ℕ} {α : ℚ} {I J : Ival} {M R : Dy} {f g : ℕ → ℝ}
    (hf : (pow a α I J).Holds N f) (hg : (geo M R).Holds N g) :
    (mulPowGeo p N a α J M R).Holds N (fun k => f k * g k) := by
  unfold mulPowGeo
  split
  · rename_i hc
    obtain ⟨hα, hNa, hR⟩ := hc
    have hR0 := Dy.nonneg_of_isNonneg hR
    split
    · rename_i jh e hjh he
      intro k hk
      obtain ⟨hpos, u, _, hJ, hfe⟩ := hf k hk
      have h2 := hg k hk
      have hNpos : (0 : ℝ) < (N : ℝ) + a := by exact_mod_cast hNa
      have hNq : (0 : ℚ) < ((N + a : ℕ) : ℚ) := by exact_mod_cast hNa
      have hq := (mem_qpowEncl p hNq α).2 e he
      have hc : (((N + a : ℕ) : ℚ) : ℝ) = (N : ℝ) + a := by push_cast; ring
      rw [hc] at hq
      have hk' : (N : ℝ) + a ≤ (k : ℝ) + a := by
        have : (N : ℝ) ≤ k := by exact_mod_cast hk
        linarith
      have hαr : (α : ℝ) ≤ 0 := by exact_mod_cast hα
      have hx := Real.rpow_le_rpow_of_nonpos hNpos hk' hαr
      have hx0 : 0 ≤ ((k : ℝ) + a) ^ (α : ℝ) := Real.rpow_nonneg hpos.le _
      have hu : |u| ≤ jh.toReal := hJ.2 jh hjh
      have hRj : 0 ≤ R.toReal ^ (k - N) := pow_nonneg hR0 _
      have hm1 := Dy.le_mulU_toReal p M e
      have hm2 := Dy.le_mulU_toReal p (mulU p M e) jh
      have hjh0 : 0 ≤ jh.toReal := le_trans (abs_nonneg u) hu
      have he0 : 0 ≤ e.toReal := le_trans hx0 (le_trans hx hq)
      have hg0 : 0 ≤ |g k| := abs_nonneg _
      show |f k * g k| ≤ _
      rw [hfe, abs_mul, abs_mul, abs_of_nonneg hx0]
      have hA : ((k : ℝ) + a) ^ (α : ℝ) * |u| ≤ e.toReal * jh.toReal :=
        mul_le_mul (le_trans hx hq) hu (abs_nonneg _) he0
      have hMR : 0 ≤ M.toReal * R.toReal ^ (k - N) := le_trans hg0 h2
      calc ((k : ℝ) + a) ^ (α : ℝ) * |u| * |g k|
          ≤ (e.toReal * jh.toReal) * (M.toReal * R.toReal ^ (k - N)) :=
            mul_le_mul hA h2 hg0 (mul_nonneg he0 hjh0)
        _ = (M.toReal * e.toReal) * jh.toReal * R.toReal ^ (k - N) := by ring
        _ ≤ (mulU p M e).toReal * jh.toReal * R.toReal ^ (k - N) := by
            apply mul_le_mul_of_nonneg_right _ hRj
            exact mul_le_mul_of_nonneg_right hm1 hjh0
        _ ≤ _ := mul_le_mul_of_nonneg_right hm2 hRj
    · trivial
  · trivial

theorem growMulConst_holds {p N : ℕ} {M R : Dy} {b : ℕ} {K L : Ival} {f g : ℕ → ℝ}
    (hf : (grow M R).Holds N f) (hg : (pow b 0 K L).Holds N g) :
    (growMulConst p M R K).Holds N (fun k => f k * g k) := by
  unfold growMulConst
  split
  · rename_i h
    simp only [Bool.and_eq_true] at h
    have hM0 := Dy.nonneg_of_isNonneg h.1; have hR0 := Dy.nonneg_of_isNonneg h.2
    split
    · rename_i l hl
      split
      · rename_i hl0
        have hl0' := Dy.nonneg_of_isNonneg hl0
        intro k hk
        have h1 := hf k hk
        obtain ⟨_, v, hv, _, hge⟩ := hg k hk
        have hgv : g k = v := by rw [hge]; simp
        have hlv : l.toReal ≤ v := hv.1 l hl
        have hRj : 0 ≤ R.toReal ^ (k - N) := pow_nonneg hR0 _
        have hm := Dy.mulD_toReal p M l
        show (mulD p M l).toReal * R.toReal ^ (k - N) ≤ f k * g k
        rw [hgv]
        have hMR : 0 ≤ M.toReal * R.toReal ^ (k - N) := mul_nonneg hM0 hRj
        calc (mulD p M l).toReal * R.toReal ^ (k - N) ≤ M.toReal * l.toReal * R.toReal ^ (k - N) :=
              mul_le_mul_of_nonneg_right hm hRj
          _ = (M.toReal * R.toReal ^ (k - N)) * l.toReal := by ring
          _ ≤ f k * v := mul_le_mul h1 hlv hl0' (le_trans hMR h1)
      · trivial
    · trivial
  · trivial

theorem mul_holds {p N : ℕ} {f g : ℕ → ℝ} {A B : RAsy} (hf : A.Holds N f) (hg : B.Holds N g) :
    (mul p N A B).Holds N (fun k => f k * g k) := by
  cases A with
  | pow a α I J =>
    cases B with
    | pow b β K L =>
      have hr := rebase_holds (p := p) (a' := a) hg
      show (match rebase p N a (pow b β K L) with
        | pow a₀ β' K' L' => if a₀ = a then pow a (α + β') (Ival.mul p I K') (Ival.mul p J L') else top
        | _ => top).Holds N _
      split
      · rename_i a₀ β' K' L' heq
        rw [heq] at hr
        split
        · rename_i ha; subst ha
          intro k hk
          obtain ⟨hpos, u, hu, hJ, hfe⟩ := hf k hk
          obtain ⟨_, v, hv, hL, hge⟩ := hr k hk
          refine ⟨hpos, u * v, Ival.mem_mul hu hv, by rw [abs_mul]; exact Ival.mem_mul hJ hL, ?_⟩
          show f k * g k = _
          rw [hfe, hge]
          have : ((k : ℝ) + a₀) ^ ((α + β' : ℚ) : ℝ) = ((k : ℝ) + a₀) ^ (α : ℝ) * ((k : ℝ) + a₀) ^ (β' : ℝ) := by
            rw [← Real.rpow_add hpos]; push_cast; ring_nf
          rw [this]; ring
        · trivial
      · trivial
    | geo M R => exact mulPowGeo_holds hf hg
    | grow M R =>
      show (if α = 0 then growMulConst p M R I else top).Holds N _
      split
      · rename_i hα; subst hα
        have e : (fun k => f k * g k) = (fun k => g k * f k) := funext fun k => mul_comm _ _
        rw [e]; exact growMulConst_holds hg hf
      · trivial
    | top => trivial
  | geo M R =>
    cases B with
    | pow a α K L =>
      have e : (fun k => f k * g k) = (fun k => g k * f k) := funext fun k => mul_comm _ _
      rw [e]; exact mulPowGeo_holds hg hf
    | geo M' R' =>
      show (if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' then
        geo (mulU p M M') (mulU p R R') else top).Holds N _
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨hM, hM'⟩, hR⟩, hR'⟩ := h
        have hM0 := Dy.nonneg_of_isNonneg hM; have hM0' := Dy.nonneg_of_isNonneg hM'
        have hR0 := Dy.nonneg_of_isNonneg hR; have hR0' := Dy.nonneg_of_isNonneg hR'
        intro k hk
        have h1 := hf k hk; have h2 := hg k hk
        have hmM := Dy.le_mulU_toReal p M M'
        have hmR := Dy.le_mulU_toReal p R R'
        have hRR0 : 0 ≤ R.toReal * R'.toReal := mul_nonneg hR0 hR0'
        have hpow : (R.toReal * R'.toReal) ^ (k - N) ≤ (mulU p R R').toReal ^ (k - N) :=
          pow_le_pow_left₀ hRR0 hmR _
        show |f k * g k| ≤ _
        rw [abs_mul]
        calc |f k| * |g k| ≤ (M.toReal * R.toReal ^ (k - N)) * (M'.toReal * R'.toReal ^ (k - N)) :=
              mul_le_mul h1 h2 (abs_nonneg _) (le_trans (abs_nonneg _) h1)
          _ = (M.toReal * M'.toReal) * (R.toReal * R'.toReal) ^ (k - N) := by rw [mul_pow]; ring
          _ ≤ (mulU p M M').toReal * (mulU p R R').toReal ^ (k - N) :=
              mul_le_mul hmM hpow (pow_nonneg hRR0 _) (le_trans (mul_nonneg hM0 hM0') hmM)
      · trivial
    | _ => trivial
  | grow M R =>
    cases B with
    | grow M' R' =>
      show (if isNonneg M && isNonneg M' && isNonneg R && isNonneg R' && isNonneg (mulD p R R') then
        grow (mulD p M M') (mulD p R R') else top).Holds N _
      split
      · rename_i h
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨⟨hM, hM'⟩, hR⟩, hR'⟩, hRR⟩ := h
        have hM0 := Dy.nonneg_of_isNonneg hM; have hM0' := Dy.nonneg_of_isNonneg hM'
        have hR0 := Dy.nonneg_of_isNonneg hR; have hR0' := Dy.nonneg_of_isNonneg hR'
        have hRR0 := Dy.nonneg_of_isNonneg hRR
        intro k hk
        have h1 := hf k hk; have h2 := hg k hk
        have hmM := Dy.mulD_toReal p M M'
        have hmR := Dy.mulD_toReal p R R'
        have hpow : (mulD p R R').toReal ^ (k - N) ≤ (R.toReal * R'.toReal) ^ (k - N) :=
          pow_le_pow_left₀ hRR0 hmR _
        have hA0 : 0 ≤ M.toReal * R.toReal ^ (k - N) := mul_nonneg hM0 (pow_nonneg hR0 _)
        have hB0 : 0 ≤ M'.toReal * R'.toReal ^ (k - N) := mul_nonneg hM0' (pow_nonneg hR0' _)
        show _ ≤ f k * g k
        calc (mulD p M M').toReal * (mulD p R R').toReal ^ (k - N)
            ≤ (M.toReal * M'.toReal) * (R.toReal * R'.toReal) ^ (k - N) := by
              rcases le_total 0 (mulD p M M').toReal with h0 | h0
              · exact mul_le_mul hmM hpow (pow_nonneg hRR0 _) (mul_nonneg hM0 hM0')
              · have : (mulD p M M').toReal * (mulD p R R').toReal ^ (k - N) ≤ 0 :=
                  mul_nonpos_of_nonpos_of_nonneg h0 (pow_nonneg hRR0 _)
                exact le_trans this (mul_nonneg (mul_nonneg hM0 hM0') (pow_nonneg (mul_nonneg hR0 hR0') _))
          _ = (M.toReal * R.toReal ^ (k - N)) * (M'.toReal * R'.toReal ^ (k - N)) := by
              rw [mul_pow]; ring
          _ ≤ f k * g k := mul_le_mul h1 h2 hB0 (le_trans hA0 h1)
      · trivial
    | pow b β K L =>
      show (if β = 0 then growMulConst p M R K else top).Holds N _
      split
      · rename_i hβ; subst hβ; exact growMulConst_holds hf hg
      · trivial
    | _ => trivial
  | top => trivial

/-! ### Inverse, powers, casts -/

def inv (p : ℕ) : RAsy → RAsy
  | pow a α I J => pow a (-α) (Ival.inv p I) (Ival.inv p J)
  | grow M R => if isPos M && isPos R then geo (divU p Dy.one M) (divU p Dy.one R) else top
  | _ => top

theorem inv_holds {p N : ℕ} {f : ℕ → ℝ} {A : RAsy} (hf : A.Holds N f) :
    (inv p A).Holds N (fun k => (f k)⁻¹) := by
  cases A with
  | pow a α I J =>
    intro k hk
    obtain ⟨hpos, u, hu, hJ, hfe⟩ := hf k hk
    refine ⟨hpos, u⁻¹, Ival.mem_inv hu, by rw [abs_inv]; exact Ival.mem_inv hJ, ?_⟩
    show (f k)⁻¹ = _
    rw [hfe, mul_inv]
    push_cast
    rw [Real.rpow_neg hpos.le]
  | grow M R =>
    show (if isPos M && isPos R then geo (divU p Dy.one M) (divU p Dy.one R) else top).Holds N _
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      have hM := Dy.pos_of_isPos h.1; have hR := Dy.pos_of_isPos h.2
      intro k hk
      have h1 := hf k hk
      have hMR : 0 < M.toReal * R.toReal ^ (k - N) := mul_pos hM (pow_pos hR _)
      have hfpos : 0 < f k := lt_of_lt_of_le hMR h1
      have hdM := Dy.one_div_le_divU p hM
      have hdR := Dy.one_div_le_divU p hR
      show |(f k)⁻¹| ≤ _
      rw [abs_of_pos (inv_pos.2 hfpos)]
      calc (f k)⁻¹ ≤ (M.toReal * R.toReal ^ (k - N))⁻¹ := inv_anti₀ hMR h1
        _ = (1 / M.toReal) * (1 / R.toReal) ^ (k - N) := by rw [mul_inv, one_div, one_div, inv_pow]
        _ ≤ _ := mul_le_mul hdM (pow_le_pow_left₀ (by positivity) hdR _) (by positivity)
            (le_trans (by positivity) hdM)
    · trivial
  | geo => trivial
  | top => trivial

def npowC (p : ℕ) (n : ℕ) : RAsy → RAsy
  | pow a α I J => pow a (α * n) (Ival.npow p I n) (Ival.npow p J n)
  | _ => top

theorem npowC_holds {p N n : ℕ} {f : ℕ → ℝ} {A : RAsy} (hf : A.Holds N f) :
    (npowC p n A).Holds N (fun k => f k ^ n) := by
  cases A with
  | pow a α I J =>
    intro k hk
    obtain ⟨hpos, u, hu, hJ, hfe⟩ := hf k hk
    refine ⟨hpos, u ^ n, Ival.mem_npow hu n, by rw [abs_pow]; exact Ival.mem_npow hJ n, ?_⟩
    show f k ^ n = _
    rw [hfe, mul_pow]
    congr 1
    push_cast
    rw [Real.rpow_mul hpos.le, Real.rpow_natCast]
  | _ => trivial

/-- `J = [1, 1]` exactly -/
def unitJ (J : Ival) : Bool :=
  match J.point? with
  | some d => Dy.leB d Dy.one && Dy.leB Dy.one d
  | none => false

theorem abs_eq_one_of_unitJ {J : Ival} {x : ℝ} (hx : x ∈ J) (h : unitJ J = true) : x = 1 := by
  unfold unitJ at h
  split at h
  · rename_i d hd
    simp only [Bool.and_eq_true] at h
    rw [Ival.eq_of_point? hx hd]
    exact le_antisymm (by simpa [toReal_def] using toReal_le_of_leB h.1)
      (by simpa [toReal_def] using toReal_le_of_leB h.2)
  · cases h

def npowKGrow (p N b : ℕ) (I : Ival) : RAsy :=
  match I.lo with
  | some l =>
    if Dy.ltB Dy.one l then
      match (Ival.npow p (Ival.pt l) (N + b)).lo with
      | some L => grow L l
      | none => top
    else top
  | none => top

def npowKGeo (p N b : ℕ) (I J : Ival) : RAsy :=
  match J.hi with
  | some h =>
    if isNonneg h && Dy.ltB h Dy.one then
      match (Ival.npow p (Ival.pt h) (N + b)).hi with
      | some H => geo H h
      | none => top
    else npowKGrow p N b I
  | none => npowKGrow p N b I

/-- `x^(k+b)` for a base with values in `I`, `|·| ∈ J` (`α = 0`) -/
def npowKPow (p N b : ℕ) (α : ℚ) (I J : Ival) : RAsy :=
  if α = 0 then
    if unitJ J then pow 1 0 ⟨some (Dy.ofInt (-1)), some Dy.one⟩ Ival.one
    else npowKGeo p N b I J
  else top

def npowK (p N b : ℕ) : RAsy → RAsy
  | pow _ α I J => npowKPow p N b α I J
  | _ => top

theorem npowKGrow_holds {p N b a : ℕ} {I J : Ival} {f : ℕ → ℝ}
    (hf : (pow a 0 I J).Holds N f) :
    (npowKGrow p N b I).Holds N (fun k => f k ^ (k + b)) := by
  unfold npowKGrow
  split
  · rename_i l hl
    split
    · rename_i h1
      have hl1 := Dy.lt_of_ltB' h1
      split
      · rename_i L hL
        intro k hk
        obtain ⟨_, u, hu, _, hfe⟩ := hf k hk
        have hfu : f k = u := by rw [hfe]; simp
        have hlu : l.toReal ≤ u := hu.1 l hl
        have hl1' : 1 < l.toReal := by simpa [toReal_def] using hl1
        have hLp : L.toReal ≤ l.toReal ^ (N + b) :=
          (Ival.mem_npow (p := p) (Ival.mem_pt l) (N + b)).1 L hL
        show L.toReal * l.toReal ^ (k - N) ≤ f k ^ (k + b)
        rw [hfu]
        have hkb : k + b = (N + b) + (k - N) := by omega
        calc L.toReal * l.toReal ^ (k - N) ≤ l.toReal ^ (N + b) * l.toReal ^ (k - N) :=
              mul_le_mul_of_nonneg_right hLp (pow_nonneg (by linarith) _)
          _ = l.toReal ^ (k + b) := by rw [← pow_add, hkb]
          _ ≤ u ^ (k + b) := pow_le_pow_left₀ (by linarith) hlu _
      · trivial
    · trivial
  · trivial

theorem npowKGeo_holds {p N b a : ℕ} {I J : Ival} {f : ℕ → ℝ}
    (hf : (pow a 0 I J).Holds N f) :
    (npowKGeo p N b I J).Holds N (fun k => f k ^ (k + b)) := by
  unfold npowKGeo
  split
  · rename_i h hh
    split
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      have hh0 := Dy.nonneg_of_isNonneg hc.1
      split
      · rename_i H hH
        intro k hk
        obtain ⟨_, u, _, hJ, hfe⟩ := hf k hk
        have hfu : f k = u := by rw [hfe]; simp
        have hu : |u| ≤ h.toReal := hJ.2 h hh
        have hHp : h.toReal ^ (N + b) ≤ H.toReal :=
          (Ival.mem_npow (p := p) (Ival.mem_pt h) (N + b)).2 H hH
        show |f k ^ (k + b)| ≤ H.toReal * h.toReal ^ (k - N)
        rw [hfu, abs_pow]
        have hkb : k + b = (N + b) + (k - N) := by omega
        calc |u| ^ (k + b) ≤ h.toReal ^ (k + b) := pow_le_pow_left₀ (abs_nonneg _) hu _
          _ = h.toReal ^ (N + b) * h.toReal ^ (k - N) := by rw [← pow_add, hkb]
          _ ≤ _ := mul_le_mul_of_nonneg_right hHp (pow_nonneg hh0 _)
      · trivial
    · exact npowKGrow_holds hf
  · exact npowKGrow_holds hf

theorem npowK_holds {p N b : ℕ} {f : ℕ → ℝ} {A : RAsy} (hf : A.Holds N f) :
    (npowK p N b A).Holds N (fun k => f k ^ (k + b)) := by
  cases A with
  | pow a α I J =>
    show (npowKPow p N b α I J).Holds N _
    unfold npowKPow
    split
    · rename_i hα; subst hα
      split
      · rename_i hunit
        intro k hk
        obtain ⟨_, u, _, hJ, hfe⟩ := hf k hk
        have hu1 : |u| = 1 := abs_eq_one_of_unitJ hJ hunit
        have hfu : f k = u := by rw [hfe]; simp
        have habs : |u ^ (k + b)| = 1 := by rw [abs_pow, hu1, one_pow]
        refine ⟨by positivity, u ^ (k + b), ?_, by rw [habs]; exact Ival.mem_one, ?_⟩
        · have := abs_le.1 (le_of_eq habs)
          refine ⟨fun l hl => ?_, fun h hh => ?_⟩
          · cases hl; simp [toReal_def]; linarith [this.1]
          · cases hh; simp [toReal_def]; linarith [this.2]
        · show f k ^ (k + b) = _
          rw [hfu]; simp
      · exact npowKGeo_holds hf
    · trivial
  | _ => trivial

def natCast (N : ℕ) : NAsy → RAsy
  | .affine b => if N + b = 0 then top else pow b 1 Ival.one Ival.one
  | .const n => const (Ival.pt (Dy.ofNat n))
  | .grow M R => grow M R
  | .top => top

theorem natCast_holds {N : ℕ} {f : ℕ → ℕ} {A : NAsy} (hf : A.Holds N f) :
    (natCast N A).Holds N (fun k => (f k : ℝ)) := by
  cases A with
  | affine b =>
    show (if N + b = 0 then top else pow b 1 Ival.one Ival.one).Holds N _
    split
    · trivial
    · rename_i hNb
      intro k hk
      have hpos : (0 : ℝ) < (k : ℝ) + b := by
        have : 0 < k + b := by omega
        exact_mod_cast this
      refine ⟨hpos, 1, Ival.mem_one, by simpa using Ival.mem_one, ?_⟩
      show (f k : ℝ) = _
      rw [hf k hk]; push_cast; simp
  | const n =>
    refine const_holds (fun k hk => ?_)
    rw [hf k hk]; simpa [toReal_def] using Ival.mem_pt (Dy.ofNat n)
  | grow M R => intro k hk; exact hf k hk
  | top => trivial

def abs : RAsy → RAsy
  | pow a α I J => pow a α (Ival.abs I) J
  | geo M R => geo M R
  | _ => top

theorem abs_holds {N : ℕ} {f : ℕ → ℝ} {A : RAsy} (hf : A.Holds N f) :
    (abs A).Holds N (fun k => |f k|) := by
  cases A with
  | pow a α I J =>
    intro k hk
    obtain ⟨hpos, u, hu, hJ, hfe⟩ := hf k hk
    refine ⟨hpos, |u|, Ival.mem_abs hu, by rwa [abs_abs], ?_⟩
    show |f k| = _
    rw [hfe, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
  | geo M R => intro k hk; show |(|f k|)| ≤ _; rw [abs_abs]; exact hf k hk
  | _ => trivial

end RAsy

/-! ### Natural-number sequences -/

namespace NAsy

def add : NAsy → NAsy → NAsy
  | affine b, const n => affine (b + n)
  | const n, affine b => affine (n + b)
  | const m, const n => const (m + n)
  | grow M R, _ => grow M R
  | _, grow M R => grow M R
  | _, _ => top

theorem add_holds {N : ℕ} {f g : ℕ → ℕ} {A B : NAsy} (hf : A.Holds N f) (hg : B.Holds N g) :
    (add A B).Holds N (fun k => f k + g k) := by
  have growL : ∀ {M R : Dy}, (grow M R).Holds N f → (grow M R).Holds N (fun k => f k + g k) :=
    fun h k hk => by
      have := h k hk
      show _ ≤ ((f k + g k : ℕ) : ℝ)
      push_cast; linarith [(Nat.cast_nonneg (g k) : (0 : ℝ) ≤ g k)]
  have growR : ∀ {M R : Dy}, (grow M R).Holds N g → (grow M R).Holds N (fun k => f k + g k) :=
    fun h k hk => by
      have := h k hk
      show _ ≤ ((f k + g k : ℕ) : ℝ)
      push_cast; linarith [(Nat.cast_nonneg (f k) : (0 : ℝ) ≤ f k)]
  cases A with
  | affine b =>
    cases B with
    | const n => intro k hk; show f k + g k = _; rw [hf k hk, hg k hk]; ring
    | grow M R => exact growR hg
    | _ => trivial
  | const m =>
    cases B with
    | affine b => intro k hk; show f k + g k = _; rw [hf k hk, hg k hk]; ring
    | const n => intro k hk; show f k + g k = _; rw [hf k hk, hg k hk]
    | grow M R => exact growR hg
    | top => trivial
  | grow M R => exact growL hf
  | top =>
    cases B with
    | grow M R => exact growR hg
    | _ => trivial

def factorial (N : ℕ) : NAsy → NAsy
  | affine b => grow (Dy.ofNat (N + b).factorial) (Dy.ofNat (N + b + 1))
  | const n => const n.factorial
  | _ => top

theorem factorial_holds {N : ℕ} {f : ℕ → ℕ} {A : NAsy} (hf : A.Holds N f) :
    (factorial N A).Holds N (fun k => (f k).factorial) := by
  cases A with
  | affine b =>
    intro k hk
    have h := Nat.factorial_mul_pow_le_factorial (m := N + b) (n := k - N)
    have e : N + b + (k - N) = f k := by rw [hf k hk]; omega
    rw [e] at h
    simp only [toReal_def, toRat_ofNat, Rat.cast_natCast]
    exact_mod_cast h
  | const n => intro k hk; show (f k).factorial = _; rw [hf k hk]
  | _ => trivial

theorem fib_three_halves (m : ℕ) : 3 * Nat.fib (m + 2) ≤ 2 * Nat.fib (m + 3) := by
  have h1 : Nat.fib (m + 3) = Nat.fib (m + 1) + Nat.fib (m + 2) := Nat.fib_add_two
  have h2 : Nat.fib (m + 2) = Nat.fib m + Nat.fib (m + 1) := Nat.fib_add_two
  have h3 : Nat.fib m ≤ Nat.fib (m + 1) := Nat.fib_mono (Nat.le_succ m)
  omega

theorem fib_ge_pow (n : ℕ) (hn : 2 ≤ n) :
    ∀ j, (Nat.fib n : ℝ) * (3 / 2 : ℝ) ^ j ≤ Nat.fib (n + j)
  | 0 => by simp
  | j + 1 => by
    have ih := fib_ge_pow n hn j
    obtain ⟨m, hm⟩ : ∃ m, n + j = m + 2 := ⟨n + j - 2, by omega⟩
    have h := fib_three_halves m
    have h' : (3 : ℝ) * Nat.fib (m + 2) ≤ 2 * Nat.fib (m + 3) := by exact_mod_cast h
    rw [show n + (j + 1) = m + 3 by omega]
    rw [show n + j = m + 2 by omega] at ih
    rw [pow_succ]
    nlinarith

def fib (N : ℕ) : NAsy → NAsy
  | affine b => if 2 ≤ N + b then grow (Dy.ofNat (Nat.fib (N + b))) ⟨3, -1⟩ else top
  | const n => const (Nat.fib n)
  | _ => top

theorem fib_holds {N : ℕ} {f : ℕ → ℕ} {A : NAsy} (hf : A.Holds N f) :
    (fib N A).Holds N (fun k => Nat.fib (f k)) := by
  cases A with
  | affine b =>
    show (if 2 ≤ N + b then grow (Dy.ofNat (Nat.fib (N + b))) ⟨3, -1⟩ else top).Holds N _
    split
    · rename_i h2
      intro k hk
      have h := fib_ge_pow (N + b) h2 (k - N)
      have e : N + b + (k - N) = f k := by rw [hf k hk]; omega
      rw [e] at h
      have h32 : (Vendor.Dyadic.toReal ⟨3, -1⟩ : ℝ) = 3 / 2 := by
        simp [toReal_def, Vendor.Dyadic.toRat, Vendor.Dyadic.pow2Nat]
      show (Dy.ofNat (Nat.fib (N + b))).toReal * (Vendor.Dyadic.toReal ⟨3, -1⟩) ^ (k - N) ≤ _
      rw [h32]
      simpa [toReal_def] using h
    · trivial
  | const n => intro k hk; show Nat.fib (f k) = _; rw [hf k hk]
  | _ => trivial

end NAsy

end Lynth.Interval
