module

public import Lean.Elab.Tactic.Cbv
public meta import Lean
public meta import Lynth.Interval.Reify.Registry
import all Lynth.Interval.Check.AiryProof
import all Lynth.Interval.Core.Expr

/-!
Kernel-checked arithmetic for the fixed eta bound certificate. Horner evaluation
avoids repeated powers; closed intermediate interval equalities are stored as
auxiliary lemmas so later checks reuse their proofs.
-/

namespace Lynth.Interval.EtaProof

def horner (p : ℕ) (X : Ival) (A : ℕ → Ival) (lo : ℕ) : ℕ → Ival
  | 0 => Ival.zero
  | n+1 => Ival.add p (A lo) (Ival.mul p X (horner p X A (lo+1) n))

theorem horner_sound {p : ℕ} {X : Ival} {x : ℝ} {A : ℕ → Ival} {a : ℕ → ℝ}
    (hx : x ∈ X) (ha : ∀ i, a i ∈ A i) (lo n : ℕ) :
    (∑ i ∈ Finset.range n, x^i * a (lo+i)) ∈ horner p X A lo n := by
  induction n generalizing lo with
  | zero => simpa only [horner, Finset.sum_range_zero] using Ival.mem_zero
  | succ n ih =>
    have he : (∑ i ∈ Finset.range (n+1), x^i * a (lo+i)) =
        a lo + x * ∑ i ∈ Finset.range n, x^i * a (lo+1+i) := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.add_zero]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      have hn : lo + (i+1) = lo+1+i := by omega
      rw [hn]
      ring
    rw [he]
    exact Ival.mem_add (ha lo) (Ival.mem_mul hx (ih (lo+1)))

namespace Kernel

public section

open Lean Meta Sym Sym.Simp
private meta def checkpoint (e : Lean.Expr) : Sym.Simp.SimpM Result := do
  if e.hasFVar || e.hasMVar || e.hasLooseBVars then return .rfl
  let .const name levels := e.getAppFn | return .rfl
  let info ← getConstInfo name
  unless info.isDefinition do return .rfl
  let body ← Meta.instantiateValueLevelParams info levels
  let body := body.beta e.getAppArgs
  let r ← Lean.Meta.Tactic.Cbv.cbvEntry body
  let value := r.getResultExpr body
  let proof ← match r with
    | .step _ h .. => pure h
    | _ => Meta.mkEqRefl body
  let ty ← Meta.mkEq e value
  let name ← Meta.mkAuxLemma [] ty proof
  return .step (← share value) (mkConst name) (done := true)
scoped cbv_simproc cbv_eval ofRat (Lynth.Interval.Ival.ofRat _ _) := checkpoint
scoped cbv_simproc cbv_eval add (Lynth.Interval.Ival.add _ _ _) := checkpoint
scoped cbv_simproc cbv_eval mul (Lynth.Interval.Ival.mul _ _ _) := checkpoint
scoped cbv_simproc cbv_eval div (Lynth.Interval.Ival.div _ _ _) := checkpoint
scoped cbv_simproc cbv_eval npow (Lynth.Interval.Ival.npow _ _ _) := checkpoint
scoped cbv_simproc cbv_eval sq (Lynth.Interval.Ival.sq _ _) := checkpoint
scoped cbv_simproc cbv_eval inv (Lynth.Interval.Ival.inv _ _) := checkpoint
scoped cbv_simproc cbv_eval horner (Lynth.Interval.EtaProof.horner _ _ _ _ _) := checkpoint
scoped cbv_simproc ↓ listGetD (List.getD _ _ _) := fun e => do
  let_expr List.getD _ _ i _ := e | return .rfl
  if (Sym.getNatValue? i).isNone then return .rfl
  let v ← Meta.whnf e
  if v == e then return .rfl
  return .step v (← Meta.mkEqRefl v)

private theorem choose_fast (n k : ℕ) : n.choose k = Nat.fast_choose n k :=
  congrFun (congrFun Nat.choose_eq_fast_choose n) k
attribute [scoped cbv_eval] choose_fast

end

end Kernel
end Lynth.Interval.EtaProof


open Lean Elab Tactic in
elab "eta_certificate" : tactic => withMainContext do
  let g ← getMainGoal
  let ty ← g.getType
  let_expr Eq _ lhs rhs := ty | throwError "eta_certificate: expected an equality"
  let r ← Meta.Tactic.Cbv.cbvEntry lhs
  let value := r.getResultExpr lhs
  unless value == rhs do throwError "eta_certificate: unexpected computed value"
  let h ← match r with
    | .step _ h .. => pure h
    | _ => Meta.mkEqRefl lhs
  g.assign h
  replaceMainGoal []
