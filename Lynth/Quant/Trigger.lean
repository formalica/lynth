import Lean
import Lynth.Euf.Procedure
import Lynth.Euf.Closure

/-!
Trigger extraction + E-matching over EUF congruence classes.

A trigger is a body subterm mentioning bound variables; matching it
against a ground term yields a substitution. Matching is syntactic,
except that subterms free of bound variables may instead match by
EUF-canonical equality (`UnionFind` over the congruence-closed edge
set). Everything downstream is kernel-checked, so the matcher itself
is trusted-but-tested oracle code.
-/
namespace Lynth.Quant

open Lean Elab Tactic Meta
open Lynth.Euf

/-- Does `e` mention any of the telescope fvars `xs` (syntactic)? -/
def mentions (xs : Array Expr) (e : Expr) : Bool :=
  Lynth.Euf.Procedure.collectSubterms e |>.any fun s => xs.any (· == s)

/-- Trigger candidates: application subterms mentioning bound vars
(largest first — `collectSubterms` is pre-order), then bare bound
fvars as a match-all fallback. -/
def extractTriggers (xs : Array Expr) (body : Expr) : List Expr :=
  let mine := Lynth.Euf.Procedure.dedup
    (Lynth.Euf.Procedure.collectSubterms body) |>.filter (mentions xs)
  let (apps, rest) := mine.partition fun e => match e with
    | .app _ _ => true
    | _ => false
  apps ++ rest

/-- Canonical representative of `e` (`0`-default for unregistered terms;
callers treat unregistered terms by syntactic equality only). -/
def canonId (atoms : Array Expr) (uf : UnionFind) (e : Expr) : Nat :=
  uf.find (Lynth.Euf.Procedure.idxOf atoms e)

/-- E-match `pat` (may mention telescope fvars `xs`) against ground `g`,
extending `subst`. Bound fvars bind on first occurrence (later
occurrences must agree syntactically or by canonical equality);
fvar-free mismatches may still match by canonical equality. -/
def matchMod (atoms : Array Expr) (uf : UnionFind) (xs : Array Expr)
    (pat g : Expr) (subst : Array (Expr × Expr)) :
    Option (Array (Expr × Expr)) := do
  if xs.any (· == pat) then
    match subst.find? fun (v, _) => v == pat with
    | some (_, e) =>
      if e == g then some subst
      else
        match atoms.findIdx? (· == e), atoms.findIdx? (· == g) with
        | some _, some _ =>
          if canonId atoms uf e == canonId atoms uf g then some subst
          else none
        | _, _ => none
    | none => some (subst.push (pat, g))
  else if pat == g then some subst
  else match pat, g with
    | .app f1 a1, .app f2 a2 =>
      let s ← matchMod atoms uf xs f1 f2 subst
      matchMod atoms uf xs a1 a2 s
    | _, _ =>
      if mentions xs pat || mentions xs g then none
      else
        match atoms.findIdx? (· == pat), atoms.findIdx? (· == g) with
        | some _, some _ =>
          if canonId atoms uf pat == canonId atoms uf g then some subst
          else none
        | _, _ => none

end Lynth.Quant
