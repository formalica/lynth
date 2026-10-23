module

public import Init.Data.Int.Basic
public import Init.Data.Nat.Bitwise.Basic
public import Init.Data.Rat.Basic
public import Init.Prelude
public import Lynth.Interval.Core.Asy
public import Lynth.Interval.Core.Ctx
public import Lynth.Interval.Core.Expr
public import Lynth.Interval.Core.Ty
public import Lynth.Interval.Num.Ival
public import Lynth.Interval.Num.NIval
import all Lynth.Interval.Core.Expr

/-!
# AIA evaluation of expressions

`e.asy c N` describes the sequence `k ↦ e.denote (ρ.push .nat k)` on
`k ≥ N` (the series index is the innermost natural variable, index `0`).
Every other variable gives no information.
-/

namespace Lynth.Interval

/-- AIA value of a variable: only the series index `var .nat 0` is known -/
@[expose] public def varAsy : (t : Ty) → ℕ → t.Asy
  | .nat, 0 => NAsy.affine 0
  | t, _ => t.asyTop

/-- AIA value of a constant with enclosure `X` -/
@[expose] public def encAsy : (t : Ty) → t.Enc → t.Asy
  | .nat, X => match NIval.isPoint X with
    | some n => NAsy.const n
    | none => NAsy.top
  | .int, _ => ()
  | .real, I => RAsy.const I
  | .cplx, _ => ()
  | .rat, _ => ()
  | .list _, _ => ()

theorem encAsy_holds {N : ℕ} : ∀ {t : Ty} {X : t.Enc} {v : t.Val}, t.Mem X v →
    t.AsyHolds N (fun _ => v) (encAsy t X)
  | .nat, X, v, h => by
    show NAsy.Holds N _ (match NIval.isPoint X with | some n => NAsy.const n | none => NAsy.top)
    split
    · rename_i n hn
      intro k _
      exact NIval.eq_of_isPoint h hn
    · trivial
  | .int, _, _, _ => trivial
  | .real, _, _, h => RAsy.const_holds (fun _ _ => h)
  | .cplx, _, _, _ => trivial
  | .rat, _, _, _ => trivial
  | .list _, _, _, _ => trivial

namespace Expr

-- AIA values of an argument list.
mutual
/-- AIA values of an argument list -/
@[expose] public def asyArgs (c : Ctx) (N : ℕ) : {tys : List Ty} → CArg tys → CAsy tys
  | _, .nil => .nil
  | (.nat :: _), .cons .nat x xs => .cons .nat (x.asy c N) (asyArgs c N xs)
  | (.int :: _), .cons .int _ xs => .cons .int () (asyArgs c N xs)
  | (.rat :: _), .cons .rat _ xs => .cons .rat () (asyArgs c N xs)
  | (.real :: _), .cons .real x xs => .cons .real (x.asy c N) (asyArgs c N xs)
  | (.cplx :: _), .cons .cplx _ xs => .cons .cplx () (asyArgs c N xs)
  | (.list _ :: _), .cons _ _ xs => .cons _ () (asyArgs c N xs)

/-- AIA evaluation -/
@[expose] public def asy (c : Ctx) (N : ℕ) : {t : Ty} → Expr t → t.Asy
  | _, .lit q => RAsy.const (Ival.ofRat c.prec q)
  | _, .rlit _ => ()
  | _, .natLit n => NAsy.const n
  | _, .intLit _ => ()
  | _, .clist _ => ()
  | _, .var t i => varAsy t i
  | _, @Expr.call tys r f xs => f.asy c N (asyArgs c N xs)
  | _, .sum t _ _ => t.asyTop
end

theorem varAsy_holds (N : ℕ) (ρ : SEnv) : ∀ (t : Ty) (i : ℕ),
    t.AsyHolds N (fun k => (ρ.push .nat k).get t i) (varAsy t i)
  | .nat, 0 => fun k _ => by simp [SEnv.push, SEnv.get]
  | .nat, _ + 1 => trivial
  | .int, _ => trivial
  | .real, _ => trivial
  | .cplx, _ => trivial
  | .rat, _ => trivial
  | .list _, _ => trivial

mutual
/-- **Soundness** of AIA evaluation. -/
theorem asy_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) :
    ∀ {t : Ty} (e : Expr t), t.AsyHolds N (fun k => e.denote (ρ.push .nat k)) (e.asy c N)
  | _, .lit q => RAsy.const_holds (fun _ _ => Ival.mem_ofRat _ _)
  | _, .rlit _ => trivial
  | _, .natLit n => fun _ _ => rfl
  | _, .intLit _ => trivial
  | _, .clist _ => trivial
  | _, .var t i => varAsy_holds N ρ t i
  | _, @Expr.call tys r f xs =>
    f.asy_sound c N _ (fun k => toVal (CArg.denoteArgs ((ρ.push .nat k)) xs)) _
      hc (fun k => f.fn_spec _) (asyArgs_sound hc N ρ xs)
  | _, .sum t _ _ => Ty.asyHolds_top t _ _

theorem asyArgs_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) :
    ∀ {tys : List Ty} (xs : CArg tys),
    CAsyHolds N (fun k => toVal (CArg.denoteArgs ((ρ.push .nat k)) xs)) (asyArgs c N xs)
  | _, .nil => trivial
  | (.nat :: _), .cons .nat x xs => by
    show _ ∧ _
    refine ⟨?_, asyArgs_sound hc N ρ xs⟩
    exact asy_sound hc N ρ x
  | (.real :: _), .cons .real x xs => by
    show _ ∧ _
    refine ⟨?_, asyArgs_sound hc N ρ xs⟩
    exact asy_sound hc N ρ x
  | (.int :: _), .cons .int _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ xs⟩
  | (.cplx :: _), .cons .cplx _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ xs⟩
  | (.rat :: _), .cons .rat _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ xs⟩
  | (.list _ :: _), .cons _ _ xs => by
    show _ ∧ _
    exact ⟨trivial, asyArgs_sound hc N ρ xs⟩
end

end Expr

end Lynth.Interval
