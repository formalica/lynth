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
  | .int, _ => ()
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
  | .int, _, _, _ => trivial
  | .real, _, _, h => RAsy.const_holds (fun _ _ => h)
  | .cplx, _, _, _ => trivial

namespace Expr

-- AIA values of an argument list.
mutual
/-- AIA values of an argument list -/
def asyArgs (c : Ctx) (N : ℕ) : {tys : List CTy} → CArg tys → CAsy tys
  | _, .nil => .nil
  | (.nat :: _), .cons .nat x xs => .cons .nat (x.asy c N) (asyArgs c N xs)
  | (.int :: _), .cons .int _ xs => .cons .int () (asyArgs c N xs)
  | (.rat :: _), .cons .rat _ xs => .cons .rat () (asyArgs c N xs)
  | (.real :: _), .cons .real x xs => .cons .real (x.asy c N) (asyArgs c N xs)

/-- AIA evaluation -/
def asy (c : Ctx) (N : ℕ) : {t : Ty} → Expr t → t.Asy
  | _, .lit q => RAsy.const (Ival.ofRat c.prec q)
  | _, .natLit n => NAsy.const n
  | _, .intLit _ => ()
  | _, .var t i => varAsy t i
  | _, .c0 f => encAsy _ (f.ev c)
  | _, .c1 f x => f.asy c N (x.asy c N)
  | _, .c2 f x y => f.asy c N (x.asy c N) (y.asy c N)
  | _, @Expr.call tys r t ht f xs => by
    subst ht
    exact f.asy c N (asyArgs c N xs)
  | _, @Expr.callRat tys f xs _ _ => f.asy c N (asyArgs c N xs)
  | _, .sum t _ _ => t.asyTop
end

theorem varAsy_holds (N : ℕ) (ρ : SEnv) : ∀ (t : Ty) (i : ℕ),
    t.AsyHolds N (fun k => (ρ.push .nat k).get t i) (varAsy t i)
  | .nat, 0 => fun k _ => by simp [SEnv.push, SEnv.get]
  | .nat, _ + 1 => trivial
  | .int, _ => trivial
  | .real, _ => trivial
  | .cplx, _ => trivial

/-- **Soundness** of AIA evaluation. -/
theorem asy_sound {c : Ctx} (hc : c.Valid) (N : ℕ) (ρ : SEnv) :
    ∀ {t : Ty} (e : Expr t), t.AsyHolds N (fun k => e.denote (ρ.push .nat k)) (e.asy c N)
  | _, .lit q => RAsy.const_holds (fun _ _ => Ival.mem_ofRat _ _)
  | _, .natLit n => fun _ _ => rfl
  | _, .intLit _ => trivial
  | _, .var t i => varAsy_holds N ρ t i
  | _, .c0 f => encAsy_holds (f.sound c _ hc f.val_spec)
  | _, .c1 f x =>
    f.asy_sound c N _ _ _ hc (fun _ => f.fn_spec _) (asy_sound hc N ρ x)
  | _, .c2 f x y =>
    f.asy_sound c N _ _ _ _ _ hc (fun _ => f.fn_spec _ _) (asy_sound hc N ρ x) (asy_sound hc N ρ y)
  | _, @Expr.call tys r t ht f xs => by
    subst ht
    exact f.asy_sound c N _ _ hc
  | _, @Expr.callRat tys f xs _ _ => f.asy_sound c N _ _ hc
  | _, .sum t _ _ => Ty.asyHolds_top t _ _

end Expr

end Lynth.Interval
