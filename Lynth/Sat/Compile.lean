import Lean
import Lynth.Sat.Differ

/-!
Generic spec compiler, fragment v1: `∀`-guarded inequalities over `Fin`.

No puzzle-specific content: matches validity predicates of the shape
`∀ i j : Fin n, guard i j = true → out i ≠ out j` (with `guard`/`out`
arbitrary terms over the bound indices, `n` a literal) and compiles
them to parameterized CNF (`cellsCNF` + per-pair `condDiffPair` with
stuck guards) with decode via `decodeVal`. Soundness/completeness flow
through `FinVal`/`Differ` plus `solveTotal`; every finite relational
puzzle instantiating the fragment — usual goals and meta
solver-functions alike — shares the compilation and the proofs.
-/
namespace Lynth.Sat.Compile

open Lean Meta
open Lynth.Sat
open Lynth.Sat.FinVal
open Lynth.Sat.Differ

/-- Fragment match result: bound, guard application info, and the two
disequal sides — all as shape roles, never puzzle-bound. -/
structure GuardNe where
  n : Nat
  guardFn : Expr
  outFn : Expr

/-- `Fin` bound literal (direct or `OfNat`-wrapped). -/
def finBound (ty : Expr) : MetaM (Option Nat) := do
  let tyR ← whnf ty
  match tyR.getAppFn with
  | .const ``Fin _ =>
    let args := tyR.getAppArgs
    if args.isEmpty then pure none
    else
      let w ← whnf args.back!
      match w with
      | .lit (.natVal n) => pure (some n)
      | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _ =>
        pure (some n)
      | _ => pure none
  | _ => pure none

/-- Match `fun input output => ∀ i j : Fin n, body` (validity lambdas
as produced by extraction): telescope peels all four binders; the
index pair must share one literal bound. Returns
`(n, g, c, i, j, body)`. -/
def matchForall2Fin (P : Expr) :
    MetaM (Option (Nat × Expr × Expr × Expr × Expr × Expr)) := do
  -- accept validity constants as well as extracted lambdas.
  -- `P` is a lambda (`fun input output => ...`); `forallTelescope`
  -- is pi-only, so peel lambdas first, then the index pis.
  let PR ← whnf P
  lambdaTelescope PR fun lams bodyLam => do
    if lams.size != 2 then pure none
    else
      -- bounded peel: exactly the two indices (an unbounded
      -- telescope would also swallow the implication hypothesis)
      forallBoundedTelescope bodyLam (some 2) fun fvs body => do
        if fvs.size != 2 then pure none
        else
          let g := lams[0]!
          let c := lams[1]!
          let i := fvs[0]!
          let j := fvs[1]!
          match ← finBound (← inferType i), ← finBound (← inferType j) with
          | some n, some m =>
            if n != m then pure none
            else if body.hasLooseBVars then pure none
            else pure (some (n, g, c, i, j, body))
          | _, _ => pure none

/-- Match the guarded-inequality body `guardApp = true → lhs ≠ rhs`.
Returns `(guardApp, lhs, rhs)`. -/
def matchGuardNeBody (body : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  match body with
  | .forallE _ dom cod _ =>
    if cod.hasLooseBVars then pure none
    else
      -- domain: `_ = true` (the stuck guard firing)
      let domR ← whnf dom
      match domR.getAppFn with
      | .const ``Eq _ =>
        let dargs := domR.getAppArgs
        if dargs.size != 3 then pure none
        else
          let guardApp := dargs[1]!
          let isTrue ← whnf dargs[2]!
          match isTrue with
          | .const ``Bool.true _ =>
            -- codomain: `lhs ≠ rhs` (`Ne`-applied; note `whnf`
            -- would unfold `Ne` away, so match the raw head first
            -- with an unfolded-`Not` fallback)
            match cod.getAppFn with
            | .const ``Ne _ =>
              let cargs := cod.getAppArgs
              if cargs.size != 3 then pure none
              else pure (some (guardApp, cargs[1]!, cargs[2]!))
            | _ =>
              let codR ← whnf cod
              match codR with
              | .app (.const ``Not _) eqProp =>
                let eqR ← whnf eqProp
                match eqR.getAppFn with
                | .const ``Eq _ =>
                  let eargs := eqR.getAppArgs
                  if eargs.size != 3 then pure none
                  else pure (some (guardApp, eargs[1]!, eargs[2]!))
                | _ => pure none
              | _ => pure none
          | _ =>
            pure none
      | _ =>
        pure none
  | _ => pure none

end Lynth.Sat.Compile
