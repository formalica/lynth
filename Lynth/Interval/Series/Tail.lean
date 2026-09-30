import Lynth.Interval.Num.Ival
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Series toolkit

* `abs_sub_sum_le_of_ratio`: tail of a series whose terms eventually decay
  geometrically.
* `serLoop`: interval partial sums via a term recurrence `t (k+1) ∈ step k (T k)`,
  stopping when the current term is small.
* `Ival.widenMag`, `Ival.magHi`, `Ival.divNat`, `Ival.mulPt`: helpers.

See `docs/interval/04-functions.md §0`.
-/

namespace Lynth.Interval

open Dy

/-- Tail bound: if `|t (k+1)| ≤ q |t k|` for all `k ≥ N`, the series differs from its
`N`-th partial sum by at most `|t N| / (1 - q)`. -/
theorem abs_sub_sum_le_of_ratio {t : ℕ → ℝ} {s : ℝ} (hs : HasSum t s) (N : ℕ) {q : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : ∀ k, N ≤ k → |t (k + 1)| ≤ q * |t k|) :
    |s - ∑ k ∈ Finset.range N, t k| ≤ |t N| / (1 - q) := by
  have hg : HasSum (fun n => t (n + N)) (s - ∑ k ∈ Finset.range N, t k) :=
    (hasSum_nat_add_iff' N).2 hs
  have hb : ∀ n, |t (n + N)| ≤ |t N| * q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := hr (n + N) (by omega)
      rw [show n + 1 + N = n + N + 1 by omega, pow_succ]
      nlinarith [abs_nonneg (t (n + N))]
  have hgeo : HasSum (fun n => |t N| * q ^ n) (|t N| * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 hq1).mul_left _
  have hneg : HasSum (fun n => -(|t N| * q ^ n)) (-(|t N| * (1 - q)⁻¹)) := hgeo.neg
  rw [abs_le, div_eq_mul_inv]
  constructor
  · exact hasSum_le (fun n => by have := abs_le.1 (hb n); linarith) hneg hg
  · exact hasSum_le (fun n => (abs_le.1 (hb n)).2) hg hgeo

namespace Ival

/-- upper bound of `|x|` over the interval (`none` if unbounded) -/
def magHi (I : Ival) : Option Dy := (abs I).hi

theorem abs_le_magHi {x : ℝ} {I : Ival} (hx : x ∈ I) {m : Dy} (hm : magHi I = some m) :
    |x| ≤ m.toReal := (mem_abs hx).2 m hm

theorem mem_pt_nat (n : ℕ) : (n : ℝ) ∈ pt (Dy.ofNat n) := by
  have := mem_pt (Dy.ofNat n); simpa [toReal_def] using this

/-- `I / n` for a positive natural `n` -/
def divNat (p : Nat) (I : Ival) (n : Nat) : Ival :=
  ⟨I.lo.map (fun a => divD p a (Dy.ofNat n)), I.hi.map (fun b => divU p b (Dy.ofNat n))⟩

theorem mem_divNat {p : Nat} {x : ℝ} {I : Ival} (hx : x ∈ I) {n : Nat} (hn : 0 < n) :
    x / n ∈ divNat p I n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnq : (Dy.ofNat n).toRat ≠ 0 := by simp; omega
  obtain ⟨hx1, hx2⟩ := hx
  rcases I with ⟨lo, hi⟩
  refine ⟨?_, ?_⟩
  · cases lo with
    | none => simp [divNat]
    | some a =>
      have ha := hx1 a rfl
      have := divD_le p a (Dy.ofNat n) hnq
      simp only [divNat, Option.map_some, loLe_some, toReal_def] at ha ⊢
      simp only [toRat_ofNat] at this
      have h' : ((divD p a (Dy.ofNat n)).toRat : ℝ) ≤ (a.toRat : ℝ) / n := by exact_mod_cast this
      exact le_trans h' (div_le_div_of_nonneg_right ha (le_of_lt hn'))
  · cases hi with
    | none => simp [divNat]
    | some b =>
      have hb := hx2 b rfl
      have := le_divU p b (Dy.ofNat n) hnq
      simp only [divNat, Option.map_some, leHi_some, toReal_def] at hb ⊢
      simp only [toRat_ofNat] at this
      have h' : (b.toRat : ℝ) / n ≤ ((divU p b (Dy.ofNat n)).toRat : ℝ) := by exact_mod_cast this
      exact le_trans (div_le_div_of_nonneg_right hb (le_of_lt hn')) h'

/-- `[lo - r, hi + r]` where `r` bounds the distance -/
def widenMag (p : Nat) (I : Ival) (r : Option Dy) : Ival :=
  match r with
  | some r => widen p I r
  | none => top

theorem mem_widenMag {p : Nat} {x v : ℝ} {I : Ival} {r : Option Dy} (hv : v ∈ I)
    (hxv : ∀ m, r = some m → |x - v| ≤ m.toReal) : x ∈ widenMag p I r := by
  cases r with
  | some m => exact mem_widen hv (hxv m rfl)
  | none => exact mem_top _

end Ival

/-! ### Partial sums by term recurrence -/

structure SerState where
  /-- index of the current term -/
  k : Nat
  /-- enclosure of `t k` -/
  T : Ival
  /-- enclosure of `∑ i < k, t i` -/
  S : Ival

/-- invariant of the series loop -/
def SerState.Inv (t : ℕ → ℝ) (st : SerState) : Prop :=
  t st.k ∈ st.T ∧ (∑ i ∈ Finset.range st.k, t i) ∈ st.S

/-- advance until `small T` or fuel runs out -/
def serLoop (p : Nat) (step : Nat → Ival → Ival) (small : Ival → Bool) :
    Nat → SerState → SerState
  | 0, st => st
  | fuel + 1, st =>
    if small st.T then st
    else serLoop p step small fuel ⟨st.k + 1, step st.k st.T, Ival.add p st.S st.T⟩

theorem serLoop_inv {p : Nat} {step : Nat → Ival → Ival} {small : Ival → Bool} {t : ℕ → ℝ}
    (hstep : ∀ k X, t k ∈ X → t (k + 1) ∈ step k X) :
    ∀ fuel st, st.Inv t → (serLoop p step small fuel st).Inv t
  | 0, _, h => h
  | fuel + 1, st, h => by
    unfold serLoop
    split
    · exact h
    · apply serLoop_inv hstep fuel
      refine ⟨hstep st.k st.T h.1, ?_⟩
      show ∑ i ∈ Finset.range (st.k + 1), t i ∈ Ival.add p st.S st.T
      rw [Finset.sum_range_succ]
      exact Ival.mem_add h.2 h.1

/-- start state `t 0 ∈ T0`, empty sum -/
def SerState.start (T0 : Ival) : SerState := ⟨0, T0, Ival.zero⟩

theorem SerState.start_inv {t : ℕ → ℝ} {T0 : Ival} (h : t 0 ∈ T0) : (SerState.start T0).Inv t :=
  ⟨h, by simpa [SerState.start] using Ival.mem_zero⟩

/-- enclosure of the series sum from a loop state, given a ratio bound `q` for the tail:
`S ± |T| · (1/(1-q))`, where `inv1q ≥ 1/(1-q)` is supplied as a dyadic. -/
def SerState.encl (p : Nat) (st : SerState) (inv1q : Dy) : Ival :=
  Ival.widenMag p st.S ((Ival.magHi st.T).map (fun m => mulU p m inv1q))

theorem SerState.mem_encl {p : Nat} {t : ℕ → ℝ} {s : ℝ} (hs : HasSum t s) {st : SerState}
    (hinv : st.Inv t) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hr : ∀ k, st.k ≤ k → |t (k + 1)| ≤ q * |t k|) {inv1q : Dy} (hinv1q : 1 / (1 - q) ≤ inv1q.toReal) :
    s ∈ st.encl p inv1q := by
  apply Ival.mem_widenMag hinv.2
  intro m hm
  simp only [Option.map_eq_some_iff] at hm
  obtain ⟨mt, hmt, rfl⟩ := hm
  have h1 := abs_sub_sum_le_of_ratio hs st.k hq0 hq1 hr
  have h2 := Ival.abs_le_magHi hinv.1 hmt
  have h3 : mt.toReal * inv1q.toReal ≤ (mulU p mt inv1q).toReal := by
    simp only [toReal_def]; exact_mod_cast le_mulU p mt inv1q
  have hpos : 0 < 1 - q := by linarith
  have h4 : |t st.k| / (1 - q) ≤ mt.toReal * inv1q.toReal := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul h2 hinv1q (by positivity) (le_trans (abs_nonneg _) h2)
  linarith

end Lynth.Interval
