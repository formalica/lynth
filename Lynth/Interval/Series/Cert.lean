import Lynth.Interval.Core.ExprAsy
import Lynth.Interval.Series.PowTail
import Lynth.Interval.Fns.Elem
import Lynth.Interval.Core.Prop

/-!
# Series certificates

`tsum f = ∑_{k<N} f k + ∑_{j≥0} f (j + N)`: the partial sum by the `sum`
evaluator, the tail from the AIA value of the body on `[N, ∞)`
(`docs/interval/08-series.md §3`).  Divergence (`¬ Summable f`) from
`|f k| ≥ c/(k+a)` or `f k ≥ M > 0` eventually.
-/

namespace Lynth.Interval.Series

open Lynth.Interval Dy

/-- enclosure of `∑_{j ≥ 0} f (j + N)` from an AIA value on `[N, ∞)` -/
def tailEncl (c : Ctx) (N : ℕ) : RAsy → Option Ival
  | .geo M R =>
    let D := subD c.prec Dy.one R
    if isNonneg M && isNonneg R && isPos D then
      let T := divU c.prec M D
      some ⟨some (Vendor.Dyadic.neg T), some T⟩
    else none
  | .pow a α I _ =>
    if α < -1 ∧ 0 < N + a ∧ I.isFinite = true then
      let C := Ival.ofRat c.prec ((N + a : ℕ) : ℚ)
      let P := Fns.rpowIval c C (Ival.ofRat c.prec α)
      let F := Ival.div c.prec (Fns.rpowIval c C (Ival.ofRat c.prec (α + 1)))
        (Ival.ofRat c.prec (-(α + 1)))
      some (Ival.mul c.prec I ⟨F.lo, (Ival.add c.prec P F).hi⟩)
    else none
  | _ => none

theorem tailEncl_sound {c : Ctx} (hc : c.Valid) {N : ℕ} {f : ℕ → ℝ} {A : RAsy}
    (hA : A.Holds N f) {T : Ival} (hT : tailEncl c N A = some T) :
    Summable (fun j => f (j + N)) ∧ ∑' j, f (j + N) ∈ T := by
  cases A with
  | geo M R =>
    simp only [tailEncl] at hT
    split at hT
    · rename_i h
      cases hT
      simp only [Bool.and_eq_true] at h
      obtain ⟨⟨hM, hR⟩, hD⟩ := h
      have hM0 := Dy.nonneg_of_isNonneg hM
      have hR0 := Dy.nonneg_of_isNonneg hR
      have hD0 := Dy.pos_of_isPos hD
      have hsub : (subD c.prec Dy.one R).toReal ≤ 1 - R.toReal := by
        have := subD_le c.prec Dy.one R
        simp only [toReal_def]; simpa using (by exact_mod_cast this : ((subD c.prec Dy.one R).toRat : ℝ) ≤ ((Dy.one.toRat - R.toRat : ℚ) : ℝ))
      have hR1 : R.toReal < 1 := by linarith
      have hbound : ∀ j, ‖f (j + N)‖ ≤ M.toReal * R.toReal ^ j := by
        intro j
        have := hA (j + N) (by omega)
        simpa [Real.norm_eq_abs] using this
      have hgs : Summable (fun j : ℕ => M.toReal * R.toReal ^ j) :=
        (summable_geometric_of_lt_one hR0 hR1).mul_left _
      have hs : Summable (fun j => f (j + N)) := Summable.of_norm_bounded hgs hbound
      refine ⟨hs, ?_⟩
      have habs : |∑' j, f (j + N)| ≤ M.toReal / (1 - R.toReal) := by
        have h1 := norm_tsum_le_tsum_norm hs.norm
        have h2 : ∑' j, ‖f (j + N)‖ ≤ ∑' j : ℕ, M.toReal * R.toReal ^ j :=
          hs.norm.tsum_le_tsum hbound hgs
        rw [tsum_mul_left, tsum_geometric_of_lt_one hR0 hR1] at h2
        rw [← Real.norm_eq_abs]
        calc ‖∑' j, f (j + N)‖ ≤ _ := h1
          _ ≤ _ := h2
          _ = _ := by rw [div_eq_mul_inv]
      have hT : M.toReal / (1 - R.toReal) ≤ (divU c.prec M (subD c.prec Dy.one R)).toReal := by
        have h1 : M.toReal / (1 - R.toReal) ≤ M.toReal / (subD c.prec Dy.one R).toReal :=
          div_le_div_of_nonneg_left hM0 hD0 hsub
        have h2 := le_divU c.prec M (subD c.prec Dy.one R) (by
          intro h0; have : (subD c.prec Dy.one R).toReal = 0 := by simp [toReal_def, h0]
          linarith)
        refine le_trans h1 ?_
        simp only [toReal_def] at h2 ⊢
        exact_mod_cast h2
      refine ⟨fun l hl => ?_, fun u hu => ?_⟩
      · cases hl
        have : -(divU c.prec M (subD c.prec Dy.one R)).toReal ≤ ∑' j, f (j + N) := by
          have := neg_abs_le (∑' j, f (j + N)); linarith
        simpa [toReal_def] using this
      · cases hu
        exact le_trans (le_abs_self _) (le_trans habs hT)
    · cases hT
  | pow a α I J =>
    simp only [tailEncl] at hT
    split at hT
    · rename_i hcond
      cases hT
      obtain ⟨hα, hNa, hI⟩ := hcond
      -- decompose the terms
      have hex : ∀ j : ℕ, ∃ u, u ∈ I ∧ f (j + N) = ((j : ℝ) + ((N + a : ℕ) : ℝ)) ^ (α : ℝ) * u := by
        intro j
        obtain ⟨_, u, hu, _, he⟩ := hA (j + N) (by omega)
        exact ⟨u, hu, by rw [he]; push_cast; ring_nf⟩
      choose u hu he using hex
      set cc : ℝ := ((N + a : ℕ) : ℝ)
      have hcc : 0 < cc := by simp only [cc]; exact_mod_cast hNa
      have hα' : (α : ℝ) < -1 := by exact_mod_cast hα
      obtain ⟨hws, hlo, hhi⟩ := powTail hα' hcc
      set w : ℕ → ℝ := fun j => ((j : ℝ) + cc) ^ (α : ℝ)
      have hw0 : ∀ j, 0 ≤ w j := fun j => Real.rpow_nonneg (by positivity) _
      -- finite bounds of I
      obtain ⟨l, hl⟩ : ∃ l, I.lo = some l := Option.isSome_iff_exists.1 (by
        simp only [Ival.isFinite, Bool.and_eq_true] at hI; exact hI.1)
      obtain ⟨h, hh⟩ : ∃ h, I.hi = some h := Option.isSome_iff_exists.1 (by
        simp only [Ival.isFinite, Bool.and_eq_true] at hI; exact hI.2)
      have hul : ∀ j, l.toReal ≤ u j := fun j => (hu j).1 l hl
      have huh : ∀ j, u j ≤ h.toReal := fun j => (hu j).2 h hh
      set B := |l.toReal| + |h.toReal|
      have hub : ∀ j, |u j| ≤ B := by
        intro j; have := hul j; have := huh j
        rw [abs_le]; constructor <;> [linarith [neg_abs_le l.toReal, abs_nonneg h.toReal];
          linarith [le_abs_self h.toReal, abs_nonneg l.toReal]]
      have hfe : ∀ j, f (j + N) = w j * u j := he
      have hs : Summable (fun j => f (j + N)) := by
        refine Summable.of_norm_bounded (hws.mul_right B) (fun j => ?_)
        rw [hfe, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 j)]
        exact mul_le_mul_of_nonneg_left (hub j) (hw0 j)
      refine ⟨hs, ?_⟩
      set S := ∑' j, w j
      set V := ∑' j, f (j + N)
      have hFpos : 0 < Series.tailF α cc := div_pos (Real.rpow_pos_of_pos hcc _) (by linarith)
      have hS : 0 < S := lt_of_lt_of_le hFpos hlo
      have hV1 : l.toReal * S ≤ V := by
        rw [← tsum_mul_left]
        refine (hws.mul_left _).tsum_le_tsum (fun j => ?_) hs
        rw [hfe, mul_comm (w j)]; exact mul_le_mul_of_nonneg_right (hul j) (hw0 j)
      have hV2 : V ≤ h.toReal * S := by
        rw [← tsum_mul_left]
        refine hs.tsum_le_tsum (fun j => ?_) (hws.mul_left _)
        rw [hfe, mul_comm (w j)]; exact mul_le_mul_of_nonneg_right (huh j) (hw0 j)
      have hQ : V / S ∈ I := by
        refine ⟨fun l' hl' => ?_, fun h' hh' => ?_⟩
        · rw [hl] at hl'; cases hl'; rw [le_div_iff₀ hS]; linarith
        · rw [hh] at hh'; cases hh'; rw [div_le_iff₀ hS]; linarith
      -- `S ∈ Z`
      have hC : cc ∈ Ival.ofRat c.prec ((N + a : ℕ) : ℚ) := by
        have := Ival.mem_ofRat c.prec ((N + a : ℕ) : ℚ); simpa [cc] using this
      have hP := Fns.mem_rpowIval hc hC (Ival.mem_ofRat c.prec α)
      have hFm : Series.tailF α cc ∈ Ival.div c.prec (Fns.rpowIval c (Ival.ofRat c.prec ((N + a : ℕ) : ℚ))
          (Ival.ofRat c.prec (α + 1))) (Ival.ofRat c.prec (-(α + 1))) := by
        have h1 := Fns.mem_rpowIval hc hC (Ival.mem_ofRat c.prec (α + 1))
        have h2 := Ival.mem_ofRat c.prec (-(α + 1))
        have := Ival.mem_div (p := c.prec) h1 h2
        unfold Series.tailF; push_cast at this ⊢; exact this
      have hZ : S ∈ (⟨(Ival.div c.prec (Fns.rpowIval c (Ival.ofRat c.prec ((N + a : ℕ) : ℚ))
          (Ival.ofRat c.prec (α + 1))) (Ival.ofRat c.prec (-(α + 1)))).lo,
          (Ival.add c.prec (Fns.rpowIval c (Ival.ofRat c.prec ((N + a : ℕ) : ℚ)) (Ival.ofRat c.prec α))
            (Ival.div c.prec (Fns.rpowIval c (Ival.ofRat c.prec ((N + a : ℕ) : ℚ))
              (Ival.ofRat c.prec (α + 1))) (Ival.ofRat c.prec (-(α + 1))))).hi⟩ : Ival) := by
        refine ⟨fun l' hl' => le_trans (hFm.1 l' hl') hlo, fun h' hh' => ?_⟩
        exact le_trans hhi ((Ival.mem_add hP hFm).2 h' hh')
      have := Ival.mem_mul (p := c.prec) hQ hZ
      rwa [div_mul_cancel₀ _ hS.ne'] at this
    · cases hT
  | grow => cases hT
  | top => cases hT

/-- enclosure of `∑' k, f k` (partial sum of `N` terms + tail) -/
def seriesEncl (c : Ctx) (body : Expr .real) (N : ℕ) : Option Ival :=
  match tailEncl c N (body.asy c N) with
  | some T => some (Ival.add c.prec ((Expr.sum .real (.natLit N) body).eval c {}) T)
  | none => none

theorem seriesEncl_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ} {S : Ival}
    (h : seriesEncl c body N = some S) :
    Summable (fun k => body.denote (({} : SEnv).push .nat k)) ∧
      ∑' k, body.denote (({} : SEnv).push .nat k) ∈ S := by
  unfold seriesEncl at h
  split at h
  · rename_i T hT
    cases h
    have hA : RAsy.Holds N (fun k => body.denote (({} : SEnv).push .nat k)) (body.asy c N) :=
      Expr.asy_sound hc N {} body
    obtain ⟨hs, hmem⟩ := tailEncl_sound hc hA hT
    have hsum := (summable_nat_add_iff (f := fun k => body.denote (({} : SEnv).push .nat k)) N).1 hs
    refine ⟨hsum, ?_⟩
    have e := Summable.sum_add_tsum_nat_add (f := fun k => body.denote (({} : SEnv).push .nat k)) N hsum
    have hp : (Expr.sum .real (.natLit N) body).denote {} ∈
        (Expr.sum .real (.natLit N) body).eval c {} :=
      Expr.eval_sound hc (Expr.sum .real (.natLit N) body) IEnv.holds_empty
    have hd : (Expr.sum .real (.natLit N) body).denote {} =
        ∑ k ∈ Finset.range N, body.denote (({} : SEnv).push .nat k) := rfl
    rw [hd] at hp
    rw [← e]
    exact Ival.mem_add hp hmem
  · cases h

/-- the value check: `|tsum f - q| < tol` -/
def seriesCheck (c : Ctx) (body : Expr .real) (N : ℕ) (q : ℚ) (tol : Expr .real) : Bool :=
  match seriesEncl c body N with
  | some S => Ival.ltB (Ival.abs (Ival.sub c.prec S (Ival.ofRat c.prec q))) (tol.eval c {})
  | none => false

theorem seriesCheck_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ} {q : ℚ}
    {tol : Expr .real} (h : seriesCheck c body N q tol = true) :
    Summable (fun k => body.denote (({} : SEnv).push .nat k)) ∧
      |∑' k, body.denote (({} : SEnv).push .nat k) - q| < tol.denote {} := by
  unfold seriesCheck at h
  split at h
  · rename_i S hS
    obtain ⟨hs, hmem⟩ := seriesEncl_sound hc hS
    refine ⟨hs, Ival.lt_of_ltB (Ival.mem_abs (Ival.mem_sub hmem (Ival.mem_ofRat _ _)))
      (Expr.eval_sound hc tol IEnv.holds_empty) h⟩
  · cases h

/-- AIA values certifying divergence -/
def divergeOk (N : ℕ) : RAsy → Bool
  | .pow a α _ J => decide (-1 ≤ α) && decide (0 < N + a) && J.pos
  | .grow M R => isPos M && Dy.leB Dy.one R
  | _ => false

/-- divergence check -/
def divergeCheck (c : Ctx) (body : Expr .real) (N : ℕ) : Bool := divergeOk N (body.asy c N)

theorem not_summable_of_asy {N : ℕ} {f : ℕ → ℝ} {A : RAsy} (hA : A.Holds N f)
    (h : divergeOk N A = true) : ¬ Summable f := by
  intro hs
  cases A with
  | pow a α I J =>
    simp only [divergeOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hα, hNa⟩, hJ⟩ := h
    obtain ⟨l, hl⟩ : ∃ l, J.lo = some l := by
      unfold Ival.pos at hJ; cases hJl : J.lo with
      | none => rw [hJl] at hJ; cases hJ
      | some l => exact ⟨l, rfl⟩
    have hl0 : 0 < l.toReal := by
      unfold Ival.pos at hJ; rw [hl] at hJ; exact Dy.pos_of_isPos hJ
    set cc : ℝ := ((N + a : ℕ) : ℝ)
    have hcc : 1 ≤ cc := by simp only [cc]; exact_mod_cast hNa
    -- `|f (j+N)| ≥ l / (j + cc)`
    have hbound : ∀ j : ℕ, l.toReal * (1 / ((j : ℝ) + cc)) ≤ |f (j + N)| := by
      intro j
      obtain ⟨hpos, u, _, hu, he⟩ := hA (j + N) (by omega)
      have hlu : l.toReal ≤ |u| := hu.1 l hl
      have e : ((j + N : ℕ) : ℝ) + a = (j : ℝ) + cc := by simp only [cc]; push_cast; ring
      rw [e] at he hpos
      have hx1 : 1 ≤ (j : ℝ) + cc := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
      have hαr : (-1 : ℝ) ≤ α := by exact_mod_cast hα
      have hp : ((j : ℝ) + cc) ^ (-1 : ℝ) ≤ ((j : ℝ) + cc) ^ (α : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hx1 hαr
      rw [Real.rpow_neg_one, ← one_div] at hp
      have hm := mul_le_mul hlu hp (by positivity) (abs_nonneg _)
      rw [he, abs_mul, abs_of_nonneg (Real.rpow_nonneg hpos.le _)]
      linarith [mul_comm (((j : ℝ) + cc) ^ (α : ℝ)) |u|]
    have hs' : Summable (fun j : ℕ => 1 / ((j : ℝ) + cc)) := by
      have h1 := ((summable_nat_add_iff (f := f) N).2 hs).abs
      have h2 : Summable (fun j : ℕ => l.toReal * (1 / ((j : ℝ) + cc))) :=
        Summable.of_nonneg_of_le (fun j => by positivity) hbound h1
      have := h2.mul_left (1 / l.toReal)
      refine this.congr (fun j => ?_)
      rw [← mul_assoc, one_div_mul_cancel hl0.ne', one_mul]
    have hs'' : Summable (fun j : ℕ => 1 / ((j + (N + a) : ℕ) : ℝ)) := by
      refine hs'.congr (fun j => ?_)
      simp only [cc, Nat.cast_add]
    have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) (N + a)).1 hs''
    exact Real.not_summable_one_div_natCast this
  | grow M R =>
    simp only [divergeOk, Bool.and_eq_true] at h
    have hM := Dy.pos_of_isPos h.1
    have hR := Dy.one_le_of_leB h.2
    have ht := hs.tendsto_atTop_zero
    have hev : ∀ᶠ k in Filter.atTop, f k < M.toReal := ht.eventually (gt_mem_nhds hM)
    obtain ⟨k, hk1, hk2⟩ := (hev.and (Filter.eventually_ge_atTop N)).exists
    have := hA k hk2
    have hRj : 1 ≤ R.toReal ^ (k - N) := one_le_pow₀ hR
    nlinarith
  | geo => simp [divergeOk] at h
  | top => simp [divergeOk] at h

theorem divergeCheck_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ}
    (h : divergeCheck c body N = true) :
    ¬ Summable (fun k => body.denote (({} : SEnv).push .nat k)) :=
  not_summable_of_asy (Expr.asy_sound hc N {} body) h

end Lynth.Interval.Series
