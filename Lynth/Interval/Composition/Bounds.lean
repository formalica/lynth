import Lynth.Interval.Series.Cert
import Lynth.Interval.Integral.NestedSound
import Lynth.Interval.Integral.NestedSearch

/-! Certified enclosures shared by arithmetic, integrals and series.
Series parameters retain their interval bounds while the natural index varies.
-/
namespace Lynth.Interval
open MeasureTheory

namespace ParametricSeries

def parameterAsy (σ : IEnv) : (t : Ty) → ℕ → t.Asy
  | .nat, 0 => NAsy.affine 0
  | .nat, i+1 => encAsy .nat (σ.get .nat i)
  | t, i => encAsy t (σ.get t i)

theorem parameterAsy_sound (N : ℕ) {ρ : SEnv} {σ : IEnv} (h : σ.Holds ρ) :
    ∀ (t : Ty) (i : ℕ), t.AsyHolds N (fun k => (ρ.push .nat k).get t i) (parameterAsy σ t i)
  | .nat, 0 => fun k _ => by simp [SEnv.push, SEnv.get]
  | .nat, i+1 => by
    simpa [parameterAsy, SEnv.push, SEnv.get] using
      (encAsy_holds (N := N) (h .nat i))
  | .int, i => trivial
  | .real, i => by
    simpa [parameterAsy, SEnv.push, SEnv.get] using
      (encAsy_holds (N := N) (h .real i))
  | .cplx, i => trivial
  | .rat, i => trivial
  | .list _, i => trivial

end ParametricSeries

namespace ParametricSeries

-- AIA values of an argument list.
mutual
/-- AIA values of an argument list -/
def asyArgs (c : Ctx) (N : ℕ) (σ : IEnv) : {tys : List Ty} → CArg tys → CAsy tys
  | _, .nil => .nil
  | (.nat :: _), .cons .nat x xs => .cons .nat (asy c N σ x) (asyArgs c N σ xs)
  | (.int :: _), .cons .int _ xs => .cons .int () (asyArgs c N σ xs)
  | (.rat :: _), .cons .rat _ xs => .cons .rat () (asyArgs c N σ xs)
  | (.real :: _), .cons .real x xs => .cons .real (asy c N σ x) (asyArgs c N σ xs)
  | (.cplx :: _), .cons .cplx _ xs => .cons .cplx () (asyArgs c N σ xs)
  | (.list _ :: _), .cons _ _ xs => .cons _ () (asyArgs c N σ xs)

/-- AIA evaluation -/
def asy (c : Ctx) (N : ℕ) (σ : IEnv) : {t : Ty} → Expr t → t.Asy
  | _, .lit q => RAsy.const (Ival.ofRat c.prec q)
  | _, .rlit _ => ()
  | _, .natLit n => NAsy.const n
  | _, .intLit _ => ()
  | _, .clist _ => ()
  | _, .var t i => parameterAsy σ t i
  | _, @Expr.call tys r f xs => f.asy c N (asyArgs c N σ xs)
  | _, .sum t _ _ => t.asyTop
end

mutual
/-- **Soundness** of AIA evaluation. -/
theorem asy_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) {σ : IEnv} (hσ : σ.Holds ρ) :
    ∀ {t : Ty} (e : Expr t), t.AsyHolds N (fun k => e.denote (ρ.push .nat k)) (asy c N σ e)
  | _, .lit q => RAsy.const_holds (fun _ _ => Ival.mem_ofRat _ _)
  | _, .rlit _ => trivial
  | _, .natLit n => fun _ _ => rfl
  | _, .intLit _ => trivial
  | _, .clist _ => trivial
  | _, .var t i => parameterAsy_sound N hσ t i
  | _, @Expr.call tys r f xs =>
    f.asy_sound c N _ (fun k => toVal (Expr.CArg.denoteArgs ((ρ.push .nat k)) xs)) _
      hc (fun k => f.fn_spec _) (asyArgs_sound hc N ρ hσ xs)
  | _, .sum t _ _ => Ty.asyHolds_top t _ _

theorem asyArgs_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) {σ : IEnv} (hσ : σ.Holds ρ) :
    ∀ {tys : List Ty} (xs : CArg tys),
    CAsyHolds N (fun k => toVal (Expr.CArg.denoteArgs ((ρ.push .nat k)) xs)) (asyArgs c N σ xs)
  | _, .nil => trivial
  | (.nat :: _), .cons .nat x xs => by
    show _ ∧ _
    refine ⟨?_, asyArgs_sound hc N ρ hσ xs⟩
    exact asy_sound hc N ρ hσ x
  | (.real :: _), .cons .real x xs => by
    show _ ∧ _
    refine ⟨?_, asyArgs_sound hc N ρ hσ xs⟩
    exact asy_sound hc N ρ hσ x
  | (.int :: _), .cons .int _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ hσ xs⟩
  | (.cplx :: _), .cons .cplx _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ hσ xs⟩
  | (.rat :: _), .cons .rat _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ hσ xs⟩
  | (.list _ :: _), .cons _ _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ hσ xs⟩
end

end ParametricSeries

namespace Composition

def covers (X Y : Ival) : Bool :=
  (match Y.lo, X.lo with
    | none, _ => true | some a, some b => Dy.leB a b | _, _ => false) &&
  (match Y.hi, X.hi with
    | none, _ => true | some a, some b => Dy.leB b a | _, _ => false)

theorem mem_of_covers {X Y : Ival} {x : ℝ} (hx : x ∈ X) (h : covers X Y = true) : x ∈ Y := by
  simp only [covers, Bool.and_eq_true] at h
  obtain ⟨hl, hu⟩ := h
  constructor
  · intro l he
    cases hX : X.lo with
    | none => simp [covers, he, hX] at hl
    | some b =>
      have hb : l.toReal ≤ b.toReal := Dy.toReal_le_of_leB (by simpa [he, hX] using hl)
      exact hb.trans (hx.1 b hX)
  · intro u he
    cases hX : X.hi with
    | none => simp [covers, he, hX] at hu
    | some b =>
      have hb : b.toReal ≤ u.toReal := Dy.toReal_le_of_leB (by simpa [he, hX] using hu)
      exact (hx.2 b hX).trans hb

def evalCheck (c : Ctx) (e : Expr .real) (σ : IEnv) (I : Ival) : Bool :=
  covers (e.eval c σ) I

theorem evalCheck_sound {c : Ctx} (hc : c.Valid) {e : Expr .real} {σ : IEnv} {ρ : SEnv}
    {x : ℝ} {I : Ival} (h : evalCheck c e σ I = true)
    (hσ : σ.Holds ρ) (hx : x = e.denote ρ) : x ∈ I := by
  rw [hx]
  exact mem_of_covers (Expr.eval_sound hc e hσ) h

theorem propCheck_sound {c : Ctx} (hc : c.Valid) {p : PropExpr} {σ : IEnv} {ρ : SEnv}
    {P : Prop} (h : p.check c σ = true)
    (hσ : σ.Holds ρ) (hp : P = p.denote ρ) : P := hp ▸ PropExpr.check_sound hc hσ h

def seriesEncl (c : Ctx) (body : Expr .real) (σ : IEnv) (N : ℕ) : Option Ival := do
  let T ← Series.tailEncl c N (ParametricSeries.asy c N σ body)
  return Ival.add c.prec ((Expr.sum .real (.natLit N) body).eval c σ) T

theorem seriesEncl_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ}
    {σ : IEnv} {ρ : SEnv} (hσ : σ.Holds ρ) {I : Ival}
    (h : seriesEncl c body σ N = some I) :
    Summable (fun k => body.denote (ρ.push .nat k)) ∧
      (∑' k, body.denote (ρ.push .nat k)) ∈ I := by
  cases ht : Series.tailEncl c N (ParametricSeries.asy c N σ body) with
  | none => simp [seriesEncl, ht] at h
  | some T =>
    have he : Ival.add c.prec ((Expr.sum .real (.natLit N) body).eval c σ) T = I := by
      simpa [seriesEncl, ht] using h
    subst I
    obtain ⟨hs, hm⟩ := Series.tailEncl_sound hc (ParametricSeries.asy_sound hc N ρ hσ body) ht
    have hs' := (summable_nat_add_iff (f := fun k => body.denote (ρ.push .nat k)) N).1 hs
    refine ⟨hs', ?_⟩
    rw [← hs'.sum_add_tsum_nat_add N]
    exact Ival.mem_add (Expr.eval_sound hc (Expr.sum .real (.natLit N) body) hσ) hm

def seriesCheck (c : Ctx) (body : Expr .real) (σ : IEnv) (N : ℕ) (I : Ival) : Bool :=
  (seriesEncl c body σ N).any (fun S => covers S I)

theorem seriesCheck_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {N : ℕ}
    {σ : IEnv} {ρ : SEnv} {f : ℕ → ℝ} {I : Ival}
    (h : seriesCheck c body σ N I = true)
    (hσ : σ.Holds ρ) (hf : ∀ k, f k = body.denote (ρ.push .nat k)) :
    Summable f ∧ (∑' k, f k) ∈ I := by
  obtain rfl : f = fun k => body.denote (ρ.push .nat k) := funext hf
  cases he : seriesEncl c body σ N with
  | none => simp [seriesCheck, he] at h
  | some J =>
    have hh := seriesEncl_sound hc hσ he
    exact ⟨hh.1, mem_of_covers hh.2 (by simpa [seriesCheck, he] using h)⟩

def integralEncl (c : Ctx) (e : Intgrl.NExpr) (env : Array Ival)
    (cert : Integral.Nested.Cert) : Option Ival := do
  if !e.scoped env.size then none else do
    let memo ← Integral.Nested.replay c cert
    Integral.Nested.evalWith c memo e env

def integralCheck (c : Ctx) (e : Intgrl.NExpr) (env : Array Ival)
    (cert : Integral.Nested.Cert) (I : Ival) : Bool :=
  (integralEncl c e env cert).any (fun J => covers J I)

theorem integralCheck_sound {c : Ctx} (hc : c.Valid) {e : Intgrl.NExpr}
    {env : Array Ival} {xs : List ℝ} {cert : Integral.Nested.Cert} {I : Ival}
    {x : ℝ} (h : integralCheck c e env cert I = true)
    (hx : Integral.Nested.EnvMem xs env) (he : x = e.real xs) : e.Converges xs ∧ x ∈ I := by
  unfold integralCheck integralEncl at h
  split at h
  · simp at h
  · rename_i hs
    cases hr : Integral.Nested.replay c cert with
    | none => simp [hr] at h
    | some memo =>
      cases hv : Integral.Nested.evalWith c memo e env with
      | none => simp [hr, hv] at h
      | some J =>
        have hh := Integral.Nested.evalWith_sound hc (Integral.Nested.replay_sound hc hr)
          (by simpa using hs) hx hv
        exact ⟨hh.1, he ▸ mem_of_covers hh.2 (by simpa [hr,hv] using h)⟩

theorem sum_zero (f : ℕ → ℝ) : (∑ k ∈ Finset.range 0, f k) = 0 := by simp

theorem sum_step (f : ℕ → ℝ) (n : ℕ) {x y : ℝ}
    (hx : (∑ k ∈ Finset.range n, f k) = x) (hy : f n = y) :
    (∑ k ∈ Finset.range (n+1), f k) = x+y := by rw [Finset.sum_range_succ, hx, hy]

theorem sum_one (f : ℕ → ℝ) {x : ℝ} (hx : f 0 = x) :
    (∑ k ∈ Finset.range 1, f k) = x := by simpa only [Finset.sum_range_one] using hx

theorem sum_split (f : ℕ → ℝ) (m n : ℕ) {x y : ℝ}
    (hx : (∑ k ∈ Finset.range m, f k) = x)
    (hy : (∑ k ∈ Finset.range n, f (m + k)) = y) :
    (∑ k ∈ Finset.range (m + n), f k) = x + y := by
  rw [Finset.sum_range_add, hx, hy]

theorem affine_integral (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in a..b, f x) = ∫ t in (0:ℝ)..1, (b - a) * f (a + (b - a) * t) := by
  rw [intervalIntegral.integral_const_mul]
  simpa [smul_eq_mul] using
    (intervalIntegral.smul_integral_comp_add_mul (f := f) (a := (0:ℝ)) (b := 1) (b-a) a).symm

theorem panel (prec : Nat) {f : ℝ → ℝ} {a b : ℚ} {I : Ival} {lo hi : Dy}
    (hm : Measurable f) (hab : a ≤ b)
    (hf : ∀ x ∈ Set.Icc (a : ℝ) b, f x ∈ I) (hlo : I.lo = some lo) (hhi : I.hi = some hi) :
    IntervalIntegrable f volume a b ∧
      (∫ x in (a : ℝ)..b, f x) ∈
        Ival.mul prec (Ival.ofRat prec (b-a)) I := by
  have hh := Intgrl.direct_enclosure (by exact_mod_cast hab) hm (fun x hx =>
    ⟨(hf x hx).1 lo hlo, (hf x hx).2 hi hhi⟩)
  refine ⟨hh.1, ?_⟩
  have hl : lo.toReal ≤ hi.toReal := by
    have hx := hf a (by constructor <;> first | exact le_rfl | exact_mod_cast hab)
    exact (hx.1 lo hlo).trans (hx.2 hi hhi)
  obtain ⟨ha, hb⟩ := hh.2
  by_cases he : a = b
  · subst b
    simpa using (Ival.mem_mul (p := prec) (Ival.mem_ofRat prec (0:ℚ)) (hf a (by simp)))
  · have hp : (0:ℝ) < (b : ℝ)-(a : ℝ) := by exact_mod_cast (sub_pos.mpr (lt_of_le_of_ne hab he))
    have hq : ((∫ x in (a : ℝ)..b, f x) / ((b : ℝ)-a)) ∈ I := by
      constructor
      · intro l heq; rw [hlo] at heq; cases heq
        exact (le_div_iff₀ hp).2 (by simpa [mul_comm] using ha)
      · intro u heq; rw [hhi] at heq; cases heq
        exact (div_le_iff₀ hp).2 (by simpa [mul_comm] using hb)
    have he := Ival.mem_mul (p := prec) (Ival.mem_ofRat prec (b-a)) hq
    simpa only [Rat.cast_sub, mul_div_cancel₀ _ (ne_of_gt hp)] using he

theorem join (prec : Nat) {f : ℝ → ℝ} {a m b : ℚ} {I J : Ival}
    (h1 : IntervalIntegrable f volume a m ∧ (∫ x in (a : ℝ)..m, f x) ∈ I)
    (h2 : IntervalIntegrable f volume m b ∧ (∫ x in (m : ℝ)..b, f x) ∈ J) :
    IntervalIntegrable f volume a b ∧
      (∫ x in (a : ℝ)..b, f x) ∈ Ival.add prec I J := by
  refine ⟨h1.1.trans h2.1, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals h1.1 h2.1]
  exact Ival.mem_add h1.2 h2.2

theorem unit_panel {f : ℝ → ℝ} {I : Ival}
    (h : IntervalIntegrable f volume ((0 : ℚ) : ℝ) ((1 : ℚ) : ℝ) ∧
      (∫ x in ((0 : ℚ) : ℝ)..((1 : ℚ) : ℝ), f x) ∈ I) :
    IntervalIntegrable f volume 0 1 ∧ (∫ x in (0 : ℝ)..1, f x) ∈ I := by
  simpa only [Rat.cast_zero, Rat.cast_one] using h


theorem hull_between {a b x : ℝ} {A B : Ival} (ha : a ∈ A) (hb : b ∈ B)
    (hx : x ∈ Set.uIcc a b) : x ∈ Ival.hull A B := by
  have h1 := Ival.mem_hull_left (J := B) ha
  have h2 := Ival.mem_hull_right (I := A) hb
  obtain h | h := Set.mem_uIcc.mp hx
  · exact ⟨fun l hl => (h1.1 l hl).trans h.1, fun u hu => h.2.trans (h2.2 u hu)⟩
  · exact ⟨fun l hl => (h2.1 l hl).trans h.1, fun u hu => h.2.trans (h1.2 u hu)⟩

theorem lengthCheck_sound (prec : Nat) {a b : ℝ} {A B : Ival} {L : Dy}
    (h : Ival.leB (Ival.abs (Ival.sub prec B A)) (Ival.pt L) = true)
    (ha : a ∈ A) (hb : b ∈ B) : |b - a| ≤ L.toReal :=
  Ival.le_of_leB (Ival.mem_abs (Ival.mem_sub (p := prec) hb ha)) (Ival.mem_pt L) h

theorem bounded_integrable {f : ℝ → ℝ} {a b C : ℝ} (hm : Measurable f)
    (hb : ∀ x ∈ Set.uIcc a b, |f x| ≤ C) : IntervalIntegrable f volume a b := by
  rcases le_total a b with hab | hab
  · exact (Intgrl.direct_enclosure hab hm (fun x hx =>
      abs_le.mp (hb x (Set.mem_uIcc.mpr (Or.inl hx))))).1
  · exact (Intgrl.direct_enclosure hab hm (fun x hx =>
      abs_le.mp (hb x (Set.mem_uIcc.mpr (Or.inr hx))))).1.symm

theorem integral_geo (prec : Nat) {f : ℕ → ℝ → ℝ} {a b : ℝ} {N : ℕ} {M R L : Dy}
    (hm : ∀ k, Measurable (f k)) (hM : 0 ≤ M.toReal) (hR : 0 ≤ R.toReal)
    (hL : |b - a| ≤ L.toReal)
    (hb : ∀ x ∈ Set.uIcc a b, (RAsy.geo M R).Holds N (fun k => f k x)) :
    (∀ k, N ≤ k → IntervalIntegrable (f k) volume a b) ∧
    (RAsy.geo (Dy.mulU prec L M) R).Holds N (fun k => ∫ x in a..b, f k x) := by
  have hL0 : 0 ≤ L.toReal := (abs_nonneg _).trans hL
  constructor
  · intro k hk
    exact bounded_integrable (hm k) (fun x hx => hb x hx k hk)
  · intro k hk
    have hp : 0 ≤ R.toReal ^ (k-N) := pow_nonneg hR _
    have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := f k)
      (a := a) (b := b) (C := M.toReal * R.toReal ^ (k-N))
      (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hb x (Set.uIoc_subset_uIcc hx) k hk)
    simp only [Real.norm_eq_abs] at hi
    calc |∫ x in a..b, f k x| ≤ M.toReal * R.toReal ^ (k-N) * |b - a| := hi
      _ ≤ L.toReal * M.toReal * R.toReal ^ (k-N) := by
        nlinarith [mul_le_mul_of_nonneg_left hL (mul_nonneg hM hp)]
      _ ≤ (Dy.mulU prec L M).toReal * R.toReal ^ (k-N) :=
        mul_le_mul_of_nonneg_right (Dy.le_mulU_toReal prec L M) hp

def symmetric (D : Dy) : Ival := ⟨some D.neg, some D⟩

def integralAsy (prec : Nat) (L : Dy) : RAsy → RAsy
  | .geo M R => if Dy.isNonneg M && Dy.isNonneg R then .geo (Dy.mulU prec L M) R else .top
  | .pow a α I _ => match (Ival.abs I).hi with
    | some B => let K := symmetric (Dy.mulU prec L B); .pow a α K (Ival.abs K)
    | none => .top
  | _ => .top

theorem integralAsy_sound (prec : Nat) {f : ℕ → ℝ → ℝ} {a b : ℕ → ℝ}
    {D : Ival} {N : ℕ} {L : Dy} {A : RAsy}
    (_hm : ∀ k, Measurable (f k)) (hL : ∀ k, N ≤ k → |b k - a k| ≤ L.toReal)
    (hd : ∀ k, N ≤ k → ∀ x ∈ Set.uIcc (a k) (b k), x ∈ D)
    (hb : ∀ x ∈ D, A.Holds N (fun k => f k x)) :
    (integralAsy prec L A).Holds N (fun k => ∫ x in a k..b k, f k x) := by
  cases A with
  | top => trivial
  | grow => trivial
  | geo M R =>
    simp only [integralAsy]
    split
    · rename_i h
      simp only [Bool.and_eq_true] at h
      have hM := Dy.nonneg_of_isNonneg h.1
      have hR := Dy.nonneg_of_isNonneg h.2
      intro k hk
      have hp : 0 ≤ R.toReal ^ (k-N) := pow_nonneg hR _
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const (f := f k)
        (a := a k) (b := b k) (C := M.toReal * R.toReal ^ (k-N))
        (fun x hx => by
          rw [Real.norm_eq_abs]
          exact hb x (hd k hk x (Set.uIoc_subset_uIcc hx)) k hk)
      simp only [Real.norm_eq_abs] at hi
      calc |∫ x in a k..b k, f k x| ≤ M.toReal * R.toReal ^ (k-N) * |b k-a k| := hi
        _ ≤ L.toReal * M.toReal * R.toReal ^ (k-N) := by
          nlinarith [mul_le_mul_of_nonneg_left (hL k hk) (mul_nonneg hM hp)]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Dy.le_mulU_toReal prec L M) hp
    · trivial
  | pow c α I J =>
    cases he : (Ival.abs I).hi with
    | none => simp [integralAsy,he,RAsy.Holds]
    | some B =>
      simp only [integralAsy,he]
      change (RAsy.pow c α (symmetric (Dy.mulU prec L B))
        (Ival.abs (symmetric (Dy.mulU prec L B)))).Holds N _
      intro k hk
      have hpos := (hb (a k) (hd k hk (a k) Set.left_mem_uIcc) k hk).1
      let w : ℝ := ((k:ℝ)+c) ^ (α:ℝ)
      have hw : 0 < w := Real.rpow_pos_of_pos hpos _
      have hu : ∀ x ∈ Set.uIcc (a k) (b k), |f k x| ≤ w * B.toReal := by
        intro x hx
        obtain ⟨_,u,hu,_,hfu⟩ := hb x (hd k hk x hx) k hk
        change f k x = w*u at hfu
        rw [hfu,abs_mul,abs_of_pos hw]
        exact mul_le_mul_of_nonneg_left ((Ival.mem_abs hu).2 B he) hw.le
      have hB0 : 0 ≤ B.toReal := by
        obtain ⟨_,u,hu,_,_⟩ := hb (a k) (hd k hk (a k) Set.left_mem_uIcc) k hk
        exact (abs_nonneg u).trans ((Ival.mem_abs hu).2 B he)
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const
        (f := f k) (a := a k) (b := b k)
        (fun x hx => by simpa only [Real.norm_eq_abs] using hu x (Set.uIoc_subset_uIcc hx))
      simp only [Real.norm_eq_abs] at hi
      have hbound : |∫ x in a k..b k, f k x| ≤ w * (Dy.mulU prec L B).toReal := by
        calc _ ≤ w*B.toReal*|b k-a k| := hi
          _ ≤ w*(L.toReal*B.toReal) := by
            nlinarith [mul_le_mul_of_nonneg_left (hL k hk) (mul_nonneg hw.le hB0)]
          _ ≤ _ := mul_le_mul_of_nonneg_left (Dy.le_mulU_toReal prec L B) hw.le
      let v := (∫ x in a k..b k, f k x)/w
      have hv : |v| ≤ (Dy.mulU prec L B).toReal := by
        rw [show |v| = |∫ x in a k..b k, f k x| / w by simp [v,abs_div,abs_of_pos hw]]
        exact (div_le_iff₀ hw).2 (by simpa [mul_comm] using hbound)
      have hmK : v ∈ symmetric (Dy.mulU prec L B) := by
        simpa [symmetric,Ival.mem_def,Ival.LoLe,Ival.LeHi,Dy.toReal_def] using abs_le.mp hv
      exact ⟨hpos,v,hmK,Ival.mem_abs hmK,(mul_div_cancel₀ _ hw.ne').symm⟩

theorem asy_source {c : Ctx} (hc : c.Valid) (body : Expr .real) {σ : IEnv} {ρ : SEnv}
    {f : ℕ → ℝ} (N : ℕ) (hσ : σ.Holds ρ)
    (hf : ∀ k, f k = body.denote (ρ.push .nat k)) :
    (ParametricSeries.asy c N σ body).Holds N f := by
  simpa only [Ty.AsyHolds, ← funext hf] using ParametricSeries.asy_sound hc N ρ hσ body

/-- A uniform real enclosure for all indices in a certified sequence tail.
This is used for bounds of integration that depend on the summation index. -/
def uniformEncl (c : Ctx) (N : ℕ) : RAsy → Option Ival
  | .geo M R =>
    if Dy.isNonneg M && Dy.isNonneg R && Dy.leB R Dy.one then some (symmetric M) else none
  | .pow a α I _ =>
    if α = 0 then some I else
    if α ≤ 0 ∧ 0 < N+a then
      let P := Fns.rpowIval c (Ival.ofRat c.prec ((N+a:ℕ):ℚ)) (Ival.ofRat c.prec α)
      some (Ival.mul c.prec I (Ival.hull Ival.zero P))
    else none
  | _ => none

theorem uniformEncl_sound {c : Ctx} (hc : c.Valid) {N : ℕ} {f : ℕ → ℝ} {A : RAsy}
    (ha : A.Holds N f) {I : Ival} (he : uniformEncl c N A = some I) :
    ∀ k, N ≤ k → f k ∈ I := by
  cases A with
  | top => cases he
  | grow => cases he
  | geo M R =>
    simp only [uniformEncl] at he
    split at he
    · rename_i h
      simp only [Bool.and_eq_true] at h
      cases he
      have hM := Dy.nonneg_of_isNonneg h.1.1
      have hR := Dy.nonneg_of_isNonneg h.1.2
      have hR1 : R.toReal ≤ 1 := by simpa [Dy.toReal_def] using Dy.toReal_le_of_leB h.2
      intro k hk
      have hab := (ha k hk).trans (by
        simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ hR hR1 (n := k-N)) hM)
      simpa [symmetric,Ival.mem_def,Ival.LoLe,Ival.LeHi,Dy.toReal_def] using abs_le.mp hab
    · cases he
  | pow a α J K =>
    simp only [uniformEncl] at he
    split at he
    · rename_i hα
      subst α
      cases he
      intro k hk
      obtain ⟨_,u,hu,_,heq⟩ := ha k hk
      change f k = _ at heq
      rw [heq]
      simpa using hu
    · split at he
      · rename_i h
        cases he
        intro k hk
        obtain ⟨hpos,u,hu,_,heq⟩ := ha k hk
        have hN : (0:ℝ) < ((N+a:ℕ):ℝ) := by exact_mod_cast h.2
        have hkN : ((N+a:ℕ):ℝ) ≤ (k:ℝ)+a := by exact_mod_cast (Nat.add_le_add_right hk a)
        have hα : (α:ℝ) ≤ 0 := by exact_mod_cast h.1
        have hp := Fns.mem_rpowIval hc (Ival.mem_ofRat c.prec ((N+a:ℕ):ℚ)) (Ival.mem_ofRat c.prec α)
        have hw : ((k:ℝ)+a)^(α:ℝ) ∈ Ival.hull Ival.zero
            (Fns.rpowIval c (Ival.ofRat c.prec ((N+a:ℕ):ℚ)) (Ival.ofRat c.prec α)) := by
          apply Ival.mem_hull_of_between Ival.mem_zero hp
          · exact (min_le_left _ _).trans (Real.rpow_nonneg hpos.le _)
          · exact (Real.rpow_le_rpow_of_nonpos hN hkN hα).trans (le_max_right _ _)
        rw [heq, mul_comm]
        exact Ival.mem_mul hu hw
      · cases he

def uniformCheck (c : Ctx) (N : ℕ) (A : RAsy) (I : Ival) : Bool :=
  (uniformEncl c N A).any (fun T => covers T I)

theorem uniformCheck_sound {c : Ctx} (hc : c.Valid) {N : ℕ} {f : ℕ → ℝ} {A : RAsy}
    {I : Ival} (h : uniformCheck c N A I = true) (ha : A.Holds N f) :
    ∀ k, N ≤ k → f k ∈ I := by
  cases he : uniformEncl c N A with
  | none => simp [uniformCheck,he] at h
  | some T =>
    intro k hk
    exact mem_of_covers (uniformEncl_sound hc ha he k hk) (by simpa [uniformCheck,he] using h)

def modelTailCheck (c : Ctx) (N : ℕ) (A : RAsy) (I : Ival) : Bool :=
  (Series.tailEncl c N A).any (fun T => covers T I)

theorem modelTailCheck_sound {c : Ctx} (hc : c.Valid) {N : ℕ} {f : ℕ → ℝ}
    {A : RAsy} {I : Ival} (h : modelTailCheck c N A I = true) (ha : A.Holds N f) :
    Summable (fun j => f (j + N)) ∧ (∑' j, f (j + N)) ∈ I := by
  cases he : Series.tailEncl c N A with
  | none => simp [modelTailCheck,he] at h
  | some T =>
    have ht := Series.tailEncl_sound hc ha he
    exact ⟨ht.1,mem_of_covers ht.2 (by simpa [modelTailCheck,he] using h)⟩

theorem model_add (p N : ℕ) {f g : ℕ → ℝ} {A B : RAsy}
    (ha : A.Holds N f) (hb : B.Holds N g) :
    (RAsy.add p N A B).Holds N (fun k => f k + g k) := RAsy.add_holds ha hb

theorem model_mul (p N : ℕ) {f g : ℕ → ℝ} {A B : RAsy}
    (ha : A.Holds N f) (hb : B.Holds N g) :
    (RAsy.mul p N A B).Holds N (fun k => f k * g k) := RAsy.mul_holds ha hb

theorem model_inv (p N : ℕ) {f : ℕ → ℝ} {A : RAsy} (ha : A.Holds N f) :
    (RAsy.inv p A).Holds N (fun k => (f k)⁻¹) := RAsy.inv_holds ha

theorem model_pow (p N n : ℕ) {f : ℕ → ℝ} {A : RAsy} (ha : A.Holds N f) :
    (RAsy.npowC p n A).Holds N (fun k => f k ^ n) := RAsy.npowC_holds ha

/-- Compose powers through multiplication, including geometric tail models. -/
def powerModel (p N : ℕ) (A : RAsy) : ℕ → RAsy
  | 0 => RAsy.const Ival.one
  | n + 1 => RAsy.mul p N (powerModel p N A n) A

theorem powerModel_sound (p N n : ℕ) {f : ℕ → ℝ} {A : RAsy} (ha : A.Holds N f) :
    (powerModel p N A n).Holds N (fun k => f k ^ n) := by
  induction n with
  | zero =>
    simp only [powerModel, pow_zero]
    exact RAsy.const_holds (fun _ _ => Ival.mem_one)
  | succ n ih =>
    simpa only [powerModel, pow_succ] using (RAsy.mul_holds (p := p) ih ha)

theorem model_eq {N : ℕ} {f g : ℕ → ℝ} {A : RAsy}
    (ha : A.Holds N g) (he : ∀ k, f k = g k) : A.Holds N f :=
  RAsy.holds_congr ha (fun k _ => (he k).symm)

theorem prefix_tail (prec : Nat) {f : ℕ → ℝ} {N : ℕ} {P T : Ival}
    (hp : (∑ k ∈ Finset.range N, f k) ∈ P)
    (ht : Summable (fun j => f (j + N)) ∧ (∑' j, f (j + N)) ∈ T) :
    Summable f ∧ (∑' k, f k) ∈ Ival.add prec P T := by
  have hs := (summable_nat_add_iff (f := f) N).1 ht.1
  refine ⟨hs, ?_⟩
  rw [← hs.sum_add_tsum_nat_add N]
  exact Ival.mem_add hp ht.2

theorem pushReal {σ : IEnv} {ρ : SEnv} {x : ℝ} {I : Ival}
    (h : σ.Holds ρ) (hx : x ∈ I) : (σ.push .real I).Holds (ρ.push .real x) :=
  h.push (t := .real) hx

theorem mem_box (prec : Nat) {a b : ℚ} {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) b) :
    x ∈ Ival.ofRats prec a b := Ival.mem_ofRats hx.1 hx.2

theorem integralConverges {k : Intgrl.NDomain} {A B E : Intgrl.NExpr} {xs : List ℝ}
    {f : ℝ → ℝ} {a b : ℝ}
    (h : (Intgrl.NExpr.integral k A B E).Converges xs)
    (hf : ∀ x, f x = E.real (xs ++ [x])) (ha : a = A.real xs) (hb : b = B.real xs) :
    k.Converges f a b := by
  obtain rfl : f = fun x => E.real (xs ++ [x]) := funext hf
  subst a; subst b
  exact h.2.2.1

theorem affine_integrable {f : ℝ → ℝ} {a b : ℝ}
    (h : IntervalIntegrable (fun t => (b - a) * f (a + (b - a) * t)) volume 0 1) :
    IntervalIntegrable f volume a b := by
  by_cases he : b-a = 0
  · have : a = b := by linarith
    simp [this]
  · have h0 : IntervalIntegrable (fun t => f (a+(b-a)*t)) volume 0 1 := by
      simpa only [← mul_assoc, inv_mul_cancel₀ he, one_mul] using h.const_mul (b-a)⁻¹
    have h1 : IntervalIntegrable (fun t => f (a+t)) volume 0 (b-a) := by
      have hh := h0.comp_mul_left (c := (b-a)⁻¹)
      simpa [mul_assoc, he] using hh
    have hh := h1.comp_add_left (-a)
    simpa [sub_eq_add_neg, add_assoc] using hh


def remainderCheck (c : Ctx) (body : Expr .real) (σ : IEnv) (N : ℕ) (I : Ival) : Bool :=
  (Series.tailEncl c N (ParametricSeries.asy c N σ body)).any (fun T => covers T I)

theorem remainderCheck_sound {c : Ctx} (hc : c.Valid) {body : Expr .real} {σ : IEnv}
    {ρ : SEnv} {f : ℕ → ℝ} {N : ℕ} {I : Ival}
    (h : remainderCheck c body σ N I = true) (hσ : σ.Holds ρ)
    (hf : ∀ k, f k = body.denote (ρ.push .nat k)) :
    Summable f ∧ (∑' k, f k) - (∑ k ∈ Finset.range N, f k) ∈ I := by
  obtain rfl : f = fun k => body.denote (ρ.push .nat k) := funext hf
  cases he : Series.tailEncl c N (ParametricSeries.asy c N σ body) with
  | none => simp [remainderCheck,he] at h
  | some T =>
    obtain ⟨hs,hm⟩ := Series.tailEncl_sound hc (ParametricSeries.asy_sound hc N ρ hσ body) he
    have hs' := (summable_nat_add_iff (f := fun k => body.denote (ρ.push .nat k)) N).1 hs
    refine ⟨hs',?_⟩
    rw [← hs'.sum_add_tsum_nat_add N,add_sub_cancel_left]
    exact mem_of_covers hm (by simpa [remainderCheck,he] using h)

theorem rewrite_remainder {f g h : ℝ → ℝ} {a b : ℝ} {T : Ival} (he : g = h)
    (hb : ∀ x ∈ Set.uIcc a b, f x - g x ∈ T) :
    ∀ x ∈ Set.uIcc a b, f x - h x ∈ T := by simpa [he] using hb

theorem integral_remainder (prec : Nat) {f p : ℝ → ℝ} {a b : ℝ} {I T : Ival} {B L : Dy}
    (hm : Measurable f) (hmp : Measurable p) (hip : IntervalIntegrable p volume a b)
    (hp : (∫ x in a..b, p x) ∈ I) (hL : |b - a| ≤ L.toReal)
    (hb : ∀ x ∈ Set.uIcc a b, f x - p x ∈ T)
    (hB : (Ival.abs T).hi = some B) :
    IntervalIntegrable f volume a b ∧
      (∫ x in a..b, f x) ∈ Ival.widen prec I (Dy.mulU prec B L) := by
  have hbound : ∀ x ∈ Set.uIcc a b, |f x-p x| ≤ B.toReal :=
    fun x hx => (Ival.mem_abs (hb x hx)).2 B hB
  have hB0 : 0 ≤ B.toReal := (abs_nonneg _).trans
    (hbound a (Set.left_mem_uIcc))
  have hie := bounded_integrable (hm.sub hmp) hbound
  have hif : IntervalIntegrable f volume a b := by
    convert hie.add hip using 1
    funext x
    exact (sub_add_cancel (f x) (p x)).symm
  refine ⟨hif, Ival.mem_widen hp ?_⟩
  rw [← intervalIntegral.integral_sub hif hip]
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun x => f x-p x) (a := a) (b := b)
    (fun x hx => by simpa only [Real.norm_eq_abs] using hbound x (Set.uIoc_subset_uIcc hx))
  simp only [Real.norm_eq_abs] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hL hB0).trans (Dy.le_mulU_toReal prec B L))

theorem local_box (prec : Nat) (lo hi : ℚ) {a b x : ℝ}
    (ha : a = (lo : ℝ)) (hb : b = (hi : ℝ)) (hx : a ≤ x) (hy : x ≤ b) :
    x ∈ Ival.ofRats prec lo hi := by
  subst a; subst b
  exact Ival.mem_ofRats hx hy

theorem transportConverges (k : Intgrl.NDomain) {f g : ℝ → ℝ} {a b c d : ℝ}
    (hf : f = g) (ha : a = c) (hb : b = d) (h : k.Converges g c d) :
    k.Converges f a b := by simpa only [hf,ha,hb] using h

theorem integral_add_bounds (prec : Nat) {f g : ℝ → ℝ} {a b : ℝ} {I J : Ival}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hi : (∫ x in a..b, f x) ∈ I) (hj : (∫ x in a..b, g x) ∈ J) :
    IntervalIntegrable (fun x => f x+g x) volume a b ∧
      (∫ x in a..b, f x+g x) ∈ Ival.add prec I J := by
  exact ⟨hf.add hg,by rw [intervalIntegral.integral_add hf hg]; exact Ival.mem_add hi hj⟩

theorem integral_sub_bounds (prec : Nat) {f g : ℝ → ℝ} {a b : ℝ} {I J : Ival}
    (hf : IntervalIntegrable f volume a b) (hg : IntervalIntegrable g volume a b)
    (hi : (∫ x in a..b, f x) ∈ I) (hj : (∫ x in a..b, g x) ∈ J) :
    IntervalIntegrable (fun x => f x-g x) volume a b ∧
      (∫ x in a..b, f x-g x) ∈ Ival.sub prec I J := by
  exact ⟨hf.sub hg,by rw [intervalIntegral.integral_sub hf hg]; exact Ival.mem_sub hi hj⟩

theorem integral_scale_bounds (prec : Nat) {f : ℝ → ℝ} {a b c : ℝ} {C I : Ival}
    (hc : c ∈ C) (hf : IntervalIntegrable f volume a b) (hi : (∫ x in a..b, f x) ∈ I) :
    IntervalIntegrable (fun x => c*f x) volume a b ∧
      (∫ x in a..b, c*f x) ∈ Ival.mul prec C I := by
  exact ⟨hf.const_mul c,by rw [intervalIntegral.integral_const_mul]; exact Ival.mem_mul hc hi⟩

theorem integral_scale_right_bounds (prec : Nat) {f : ℝ → ℝ} {a b c : ℝ} {C I : Ival}
    (hf : IntervalIntegrable f volume a b) (hi : (∫ x in a..b, f x) ∈ I) (hc : c ∈ C) :
    IntervalIntegrable (fun x => f x*c) volume a b ∧
      (∫ x in a..b, f x*c) ∈ Ival.mul prec I C := by
  exact ⟨hf.mul_const c,by rw [intervalIntegral.integral_mul_const]; exact Ival.mem_mul hi hc⟩

theorem integral_div_bounds (prec : Nat) {f : ℝ → ℝ} {a b c : ℝ} {C I : Ival}
    (hf : IntervalIntegrable f volume a b) (hi : (∫ x in a..b, f x) ∈ I) (hc : c ∈ C) :
    IntervalIntegrable (fun x => f x/c) volume a b ∧
      (∫ x in a..b, f x/c) ∈ Ival.div prec I C := by
  exact ⟨hf.div_const c,by rw [intervalIntegral.integral_div]; exact Ival.mem_div hi hc⟩

theorem emptyEnvMem : Integral.Nested.EnvMem [] #[] := ⟨rfl, by simp⟩

theorem mem_transport {a b : ℝ} {I : Ival} (he : a = b) (hb : b ∈ I) : a ∈ I := he ▸ hb

end Composition
end Lynth.Interval
