import Lean
import Lynth.Procedure
import Lynth.Egraph.Procedure
import Lynth.Euf.Procedure
import Lynth.FinSearch.Procedure
import Lynth.FinSearch.ListInfer
import Lynth.Witness

/-!
Answer-goal procedure: split `Sum`/`PSum` goals (notably the FinDomain
`Answer` shape `{ w // p w } ⊕' (∀ x, ¬ p x)`) into refutation and
witness branches.

- Right branch: `refine inr`; first finite `decide` refutation on the
  `∀`-goal (under a cardinality guard), otherwise `intros` and egraph
  split-free refutation.
- Left branch: `refine inl`, then the synthesis sub-pipeline
  (`finsearch`, `listsynth`, `witness`) on the `Subtype` goal.

Every failed attempt restores the snapshot, so falling through leaves
the goal untouched for later procedures.
-/
namespace Lynth.Answer.Procedure

open Lean Elab Tactic Meta

/-- If the goal whnf-unfolds to `Sum`/`PSum`, return `isPSum`. -/
def isSumGoal : TacticM (Option Bool) := do
  let t ← whnf (← getMainTarget)
  match t with
  | .app (.app (.const ``PSum _) _) _ => pure (some true)
  | .app (.app (.const ``Sum _) _) _ => pure (some false)
  | _ => pure none

/-- Bounded power: `none` as soon as the result exceeds `lim`
(keeps estimation fast on huge exponents). -/
def powLim (b : Nat) : Nat → Nat → Option Nat
  | 0, _ => some 1
  | e + 1, lim =>
    if b == 0 then some 0
    else if b == 1 then some 1
    else match powLim b e lim with
      | none => none
      | some r =>
        let r := r * b
        if r > lim then none else some r

/-- Max domain size for `decide` refutation (bigger spaces hang CI). -/
def maxDecideCard : Nat := 100000

/-- Structural core: direct subterms only, so structural recursion holds. -/
def estCardCore (lim : Nat) : Expr → MetaM (Option Nat)
  | .app (.app (.const ``Prod _) α) β => do
    match ← estCardCore lim α with
    | none => pure none
    | some a => match ← estCardCore lim β with
      | none => pure none
      | some b => pure (if a * b > lim then none else some (a * b))
  | .app (.app (.const ``Sum _) α) β => do
    match ← estCardCore lim α with
    | none => pure none
    | some a => match ← estCardCore lim β with
      | none => pure none
      | some b => pure (if a + b > lim then none else some (a + b))
  | .forallE _ d b _ =>
    if b.hasLooseBVars then pure none
    else do
      match ← estCardCore lim d with
      | none => pure none
      | some dc => match ← estCardCore lim b with
        | none => pure none
        | some cc => pure (powLim cc dc lim)
  | .app (.const ``Fin _) n => do
    let n ← whnfR n
    match n with
    | .lit (.natVal k) => pure (some k)
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _ => pure (some k)
    | _ => pure none
  | .const ``Bool _ => pure (some 2)
  | .app (.app (.const ``Subtype _) α) _ => estCardCore lim α
  | _ => pure none

/-- Structural cardinality estimate for finite domain types. Never
evaluates kernel terms (evaluating `Finset.univ.card` constructively
explodes); overestimates only in the safe direction (`Subtype` uses
its base). `none` for infinite or unknown shapes. -/
def estCard (lim : Nat) (e : Expr) : MetaM (Option Nat) := do
  estCardCore lim (← whnfR e)

/-- Cardinality guard for finite refutation: `some n` for small finite
domains (then `decide` is feasible), `none` otherwise. -/
def domainCard (α : Expr) : MetaM (Option Nat) :=
  estCard maxDecideCard α

/-- Finite refutation of a `∀`-goal: unfold head definitions, then
`decide`. Only runs under the cardinality guard. -/
def tryDecideForall : TacticM Bool := do
  let target ← whnf (← getMainTarget)
  match target with
  | .forallE _ α _ _ =>
    match ← domainCard α with
    | none => pure false
    | some n =>
      if n > maxDecideCard then return false
      -- collect unfoldable definitions in the target (bounded)
      let mut defs := #[]
      for s in Lynth.Euf.Procedure.collectSubterms target do
        if defs.size ≥ 8 then break
        match s with
        | .const c _ =>
          if (c.toString.startsWith "inst") then continue
          match (← getEnv).find? c with
          | some (.defnInfo _) =>
            if !(defs.any fun id => id.getId == c) then defs := defs.push (mkIdent c)
          | _ => pure ()
        | _ => pure ()
      try
        unless defs.isEmpty do
          evalTactic (← `(tactic| unfold $defs*))
        evalTactic (← `(tactic| decide))
        pure (← getUnsolvedGoals).isEmpty
      catch _ => pure false
  | _ => pure false

/-- Right branch: `refine inr`. First try finite `decide` refutation on
the `∀`-goal; otherwise `intros` and egraph split-free refutation.
True if closed. -/
def tryInr (isPSum : Bool) : TacticM Bool := do
  let snapshot ← saveState
  try
    let ctor := if isPSum then ``PSum.inr else ``Sum.inr
    evalTactic (← `(tactic| refine $(mkIdent ctor) ?_))
    if ← tryDecideForall then return true
    evalTactic (← `(tactic| intros))
    let t ← whnfR (← getMainTarget)
    unless t.isConstOf ``False do
      restoreState snapshot
      return false
    match ← Lynth.Egraph.Procedure.run with
    | .success => return true
    | .failure _ =>
      restoreState snapshot
      return false
  catch _ =>
    restoreState snapshot
    return false

/-- Left branch: `refine inl`, then synthesis sub-pipeline on the
`Subtype` goal. True if closed. -/
def tryInl (isPSum : Bool) : TacticM Bool := do
  let snapshot ← saveState
  try
    let ctor := if isPSum then ``PSum.inl else ``Sum.inl
    evalTactic (← `(tactic| refine $(mkIdent ctor) ?_))
    let procs := [Lynth.FinSearch.Procedure.run,
                  Lynth.FinSearch.ListInfer.run,
                  Lynth.Witness.run]
    for proc in procs do
      try
        match ← proc with
        | .success => return true
        | .failure _ => pure ()
      catch _ => pure ()
    restoreState snapshot
    return false
  catch _ =>
    restoreState snapshot
    return false

/-- Split answer goals; pass everything else through untouched. -/
def run : TacticM ProcedureOutcome := do
  match ← isSumGoal with
  | none => return .failure []
  | some isPSum =>
    if ← tryInr isPSum then return .success
    if ← tryInl isPSum then return .success
    return .failure []

end Lynth.Answer.Procedure
