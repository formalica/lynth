import Lynth.Interval.Integral.Math.Integrand
import Lynth.Interval.Integral.Math.IntegralBounds

/-! Portable tail models and integral assembly contracts. -/

namespace Intgrl

inductive TailFamily where
  | gaussian (power : ℕ)
  | exponential (power : ℕ)
  | sech (power : ℕ)
  | arctan
  | airyDamped
deriving Repr, Inhabited

structure TailModel where
  family : TailFamily
  scale : ℚ := 1
deriving Repr, Inhabited

def gaussianTerm : Term := .unary .exp (.unary .neg (.pow .var 2))
def exponentialTerm : Term := .unary .exp (.unary .neg .var)

def classifyTail : Term → Option TailModel
  | .binary .mul (.unary .exp (.unary .neg .var)) (.unary .airyAi (.unary .neg .var))
  | .binary .mul (.unary .airyAi (.unary .neg .var)) (.unary .exp (.unary .neg .var)) =>
      some ⟨.airyDamped,1⟩
  | .unary .exp (.unary .neg (.pow .var 2)) => some ⟨.gaussian 0,1⟩
  | .unary .exp (.unary .neg .var) => some ⟨.exponential 0,1⟩
  | .binary .mul (.unary .exp (.unary .neg (.pow .var 2))) (.pow .var n) =>
      some ⟨.gaussian n,1⟩
  | .binary .mul (.pow .var n) (.unary .exp (.unary .neg (.pow .var 2))) =>
      some ⟨.gaussian n,1⟩
  | .binary .mul (.unary .exp (.unary .neg .var)) (.pow .var n) =>
      some ⟨.exponential n,1⟩
  | .binary .mul (.pow .var n) (.unary .exp (.unary .neg .var)) =>
      some ⟨.exponential n,1⟩
  | .unary .inv (.unary .cosh .var) => some ⟨.sech 1,1⟩
  | .binary .div (.rat q) (.unary .cosh .var) => some ⟨.sech 1,q⟩
  | .pow (.unary .inv (.unary .cosh .var)) n =>
      if n > 0 then some ⟨.sech n,1⟩ else none
  | .binary .div (.rat q) (.binary .add (.rat p) (.pow .var 2)) =>
      if p == 1 then some ⟨.arctan,q⟩ else none
  | _ => none

def gaussianBoundTerm : ℕ → Term
  | 0 => .binary .div gaussianTerm (.binary .mul (.rat 2) .var)
  | 1 => .binary .div gaussianTerm (.rat 2)
  | n + 2 => .binary .div
      (.binary .add (.binary .mul (.pow .var (n+1)) gaussianTerm)
        (.binary .mul (.rat (n+1)) (gaussianBoundTerm n))) (.rat 2)

def TailModel.boundTerm (m : TailModel) : Term :=
  .binary .mul (.rat |m.scale|) (match m.family with
    | .gaussian n => gaussianBoundTerm n
    | .exponential n =>
      .binary .mul exponentialTerm
        ((List.range (n+1)).foldr (fun j acc =>
          .binary .add (.binary .mul (.rat ((n.factorial : ℚ) / j.factorial))
            (.pow .var j)) acc) (.rat 0))
    | .sech n => .binary .mul (.rat ((2 : ℚ)^n / n))
        (.unary .exp (.unary .neg (.binary .mul (.rat n) .var)))
    | .arctan => .unary .inv .var
    | .airyDamped => exponentialTerm)

def TailModel.twoSided : TailModel → Bool
  | ⟨.gaussian _,_⟩ => true
  | _ => false

theorem tailModel_sound {e : Term} {m : TailModel}
    (h : classifyTail e = some m) {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn e.real (Set.Ioi R) ∧
      |(∫ x in Set.Ioi R, e.real x)| ≤ m.boundTerm.real R := by
  sorry

theorem tailModel_left_sound {e : Term} {m : TailModel}
    (h : classifyTail e = some m) (hs : m.twoSided = true)
    {R : ℝ} (hR : 0 < R) :
    MeasureTheory.IntegrableOn e.real (Set.Iio (-R)) ∧
      |(∫ x in Set.Iio (-R), e.real x)| ≤ m.boundTerm.real R := by
  sorry

theorem halfline_assembly {f : ℝ → ℝ} {a R E : ℝ}
    (haR : a ≤ R) (hm : IntervalIntegrable f MeasureTheory.volume a R)
    (ht : MeasureTheory.IntegrableOn f (Set.Ioi R))
    (he : |(∫ x in Set.Ioi R, f x)| ≤ E) :
    MeasureTheory.IntegrableOn f (Set.Ioi a) ∧
      |(∫ x in Set.Ioi a, f x) - (∫ x in a..R, f x)| ≤ E := by
  sorry

theorem wholeline_assembly {f : ℝ → ℝ} {R L U : ℝ} (hR : 0 < R)
    (hm : IntervalIntegrable f MeasureTheory.volume (-R) R)
    (hl : MeasureTheory.IntegrableOn f (Set.Iio (-R)))
    (hu : MeasureTheory.IntegrableOn f (Set.Ioi R))
    (hL : |(∫ x in Set.Iio (-R), f x)| ≤ L)
    (hU : |(∫ x in Set.Ioi R, f x)| ≤ U) :
    MeasureTheory.IntegrableOn f Set.univ ∧
      |(∫ x, f x) - (∫ x in (-R)..R, f x)| ≤ L + U := by
  sorry

end Intgrl
