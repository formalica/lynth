import Lynth.Interval.Core.Expr

/-!
# AIA evaluation of expressions

`e.asy c N` describes the sequence `k ↦ e.denote (ρ.push .nat k)` on
`k ≥ N` (the series index is the innermost natural variable, index `0`).
Every other variable gives no information.
-/

namespace Lynth.Interval

/-- AIA value of a variable: only the series index `var .nat 0` is known -/
def varAsy : (t : Ty) → ℕ → t.Asy
  | .nat, 0 => NAsy.affine 0
  | t, _ => t.asyTop

/-- AIA value of a constant with enclosure `X` -/
def encAsy : (t : Ty) → t.Enc → t.Asy
  | .nat, X => match NIval.isPoint X with
    | some n => NAsy.const n
    | none => NAsy.top
  | .real, I => RAsy.const I
  | .cplx, _ => ()

theorem encAsy_holds {N : ℕ} : ∀ {t : Ty} {X : t.Enc} {v : t.Val}, t.Mem X v →
    t.AsyHolds N (fun _ => v) (encAsy t X)
  | .nat, X, v, h => by
    show NAsy.Holds N _ (match NIval.isPoint X with | some n => NAsy.const n | none => NAsy.top)
    split
    · rename_i n hn
      intro k _
      exact NIval.eq_of_isPoint h hn
    · trivial
  | .real, _, _, h => RAsy.const_holds (fun _ _ => h)
  | .cplx, _, _, _ => trivial

namespace Expr

/-- AIA evaluation -/
def asy (c : Ctx) (N : ℕ) : {t : Ty} → Expr t → t.Asy
  | _, .lit q => RAsy.const (Ival.ofRat c.prec q)
  | _, .natLit n => NAsy.const n
  | _, .var t i => varAsy t i
  | _, .c0 f => encAsy _ (f.ev c)
  | _, .c1 f x => f.asy c N (x.asy c N)
  | _, .c2 f x y => f.asy c N (x.asy c N) (y.asy c N)
  | _, .sum t _ _ => t.asyTop

theorem varAsy_holds (N : ℕ) (ρ : SEnv) : ∀ (t : Ty) (i : ℕ),
    t.AsyHolds N (fun k => (ρ.push .nat k).get t i) (varAsy t i)
  | .nat, 0 => fun k _ => by simp [SEnv.push, SEnv.get]
  | .nat, _ + 1 => trivial
  | .real, _ => trivial
  | .cplx, _ => trivial

/-- **Soundness** of AIA evaluation. -/
theorem asy_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) :
    ∀ {t : Ty} (e : Expr t), t.AsyHolds N (fun k => e.denote (ρ.push .nat k)) (e.asy c N)
  | _, .lit q => RAsy.const_holds (fun _ _ => Ival.mem_ofRat _ _)
  | _, .natLit n => fun _ _ => rfl
  | _, .var t i => varAsy_holds N ρ t i
  | _, .c0 f => encAsy_holds (f.sound c _ hc f.val_spec)
  | _, .c1 f x =>
    f.asy_sound c N _ _ _ hc (fun _ => f.fn_spec _) (asy_sound hc N ρ x)
  | _, .c2 f x y =>
    f.asy_sound c N _ _ _ _ _ hc (fun _ => f.fn_spec _ _) (asy_sound hc N ρ x) (asy_sound hc N ρ y)
  | _, .sum t _ _ => Ty.asyHolds_top t _ _

end Expr

end Lynth.Interval
