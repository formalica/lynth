import Lynth.Interval.Core.Ctx
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Asymptotic interval arithmetic (AIA): value types

An AIA value describes a whole sequence tail `k ≥ N` at once
(`docs/interval/08-series.md §2`):

* `RAsy.pow a α I J`: `f k = (k + a)^α · u` with `u ∈ I`, `|u| ∈ J`
  (`J` keeps magnitude information through sign alternation, e.g. `(-1)^k`);
* `RAsy.geo M R`:    `|f k| ≤ M · R^(k-N)`;
* `RAsy.grow M R`:   `M · R^(k-N) ≤ f k`;
* `NAsy.affine b`:   `n k = k + b`; `NAsy.const n`; `NAsy.grow M R`.

Functions register AIA rules through the `asy` / `asy_sound` fields of
`Fn1`/`Fn2` (default: no information).
-/

namespace Lynth.Interval

/-- asymptotic enclosure of a real sequence on `[N, ∞)` -/
inductive RAsy where
  | pow (a : ℕ) (α : ℚ) (I J : Ival)
  | geo (M R : Dy)
  | grow (M R : Dy)
  | top

/-- asymptotic description of a natural-number sequence on `[N, ∞)` -/
inductive NAsy where
  | affine (b : ℕ)
  | const (n : ℕ)
  | grow (M R : Dy)
  | top

namespace RAsy

def Holds (N : ℕ) (f : ℕ → ℝ) : RAsy → Prop
  | pow a α I J => ∀ k, N ≤ k →
      0 < (k : ℝ) + a ∧ ∃ u, u ∈ I ∧ |u| ∈ J ∧ f k = ((k : ℝ) + a) ^ (α : ℝ) * u
  | geo M R => ∀ k, N ≤ k → |f k| ≤ M.toReal * R.toReal ^ (k - N)
  | grow M R => ∀ k, N ≤ k → M.toReal * R.toReal ^ (k - N) ≤ f k
  | top => True

/-- a sequence with values in `I` -/
def const (I : Ival) : RAsy := pow 1 0 I (Ival.abs I)

theorem const_holds {N : ℕ} {f : ℕ → ℝ} {I : Ival} (h : ∀ k, N ≤ k → f k ∈ I) :
    (const I).Holds N f := by
  intro k hk
  refine ⟨by positivity, f k, h k hk, Ival.mem_abs (h k hk), ?_⟩
  simp

end RAsy

namespace NAsy

def Holds (N : ℕ) (f : ℕ → ℕ) : NAsy → Prop
  | affine b => ∀ k, N ≤ k → f k = k + b
  | const n => ∀ k, N ≤ k → f k = n
  | grow M R => ∀ k, N ≤ k → M.toReal * R.toReal ^ (k - N) ≤ (f k : ℝ)
  | top => True

end NAsy

/-- AIA values by type (complex: no information yet) -/
@[reducible] def Ty.Asy : Ty → Type
  | .nat => NAsy
  | .real => RAsy
  | .cplx => Unit

def Ty.asyTop : (t : Ty) → t.Asy
  | .nat => NAsy.top
  | .real => RAsy.top
  | .cplx => ()

def Ty.AsyHolds : (t : Ty) → ℕ → (ℕ → t.Val) → t.Asy → Prop
  | .nat, N, f, A => NAsy.Holds N f A
  | .real, N, f, A => RAsy.Holds N f A
  | .cplx, _, _, _ => True

theorem Ty.asyHolds_top : (t : Ty) → (N : ℕ) → (f : ℕ → t.Val) → t.AsyHolds N f t.asyTop
  | .nat, _, _ => trivial
  | .real, _, _ => trivial
  | .cplx, _, _ => trivial

end Lynth.Interval
