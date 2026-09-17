import Lean
import Lynth.Procedure
import Lynth.Euf.Procedure
import Lynth.Euf.Closure
import Lynth.Quant.Trigger

/-!
`Quant` procedure: E-matching ground instantiation for `∀`-hypotheses.

Each dependent `∀`-hypothesis yields triggers (body subterms mentioning
bound variables); triggers are matched against ground terms from the
goal and context, modulo EUF congruence classes. Matches become proven
instances (`hyp arg…`) asserted as hypotheses for later procedures —
soundness is free because the kernel checks every instance. Single
pass, fully bounded (no fixpoint): this procedure enriches the context
and always yields to the next one.
-/
namespace Lynth.Quant.Procedure

open Lean Elab Tactic Meta
open Lynth.Euf
open Lynth.Quant

/-- A universally quantified hypothesis (closed type; opened per use). -/
structure ForallHyp where
  proof : Expr
  ty : Expr

/-- Collect dependent `∀`-hyps (default kind only, skipping the
`_example` self-reference like every other collector). -/
def collectForalls : TacticM (Array ForallHyp) := do
  let mut out := #[]
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      let ty ← whnfR decl.type
      match ty with
      | .forallE _ _ b _ =>
        if b.hasLooseBVars then
          let prf := match decl with
            | .ldecl _ fvarId _ _ _ _ _ => Expr.fvar fvarId
            | .cdecl _ fvarId _ _ _ _ => Expr.fvar fvarId
          out := out.push { proof := prf, ty }
        else pure ()
      | _ => pure ()
  pure out

/-- Ground-term pool: subterms of goal + default-kind hyp types without
loose bound variables, plus the free variables themselves,
deduplicated and capped. -/
def groundPool (cap : Nat := 64) : TacticM (Array Expr) := do
  let mut atoms : Array Expr := #[]
  let goal ← getMainTarget
  for s in Lynth.Euf.Procedure.collectSubterms goal do
    if !s.hasLooseBVars then
      if (atoms.findIdx? (· == s)).isNone then atoms := atoms.push s
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      let fv := match decl with
        | .ldecl _ fvarId _ _ _ _ _ => Expr.fvar fvarId
        | .cdecl _ fvarId _ _ _ _ => Expr.fvar fvarId
      if (atoms.findIdx? (· == fv)).isNone then atoms := atoms.push fv
      for s in Lynth.Euf.Procedure.collectSubterms decl.type do
        if !s.hasLooseBVars then
          if (atoms.findIdx? (· == s)).isNone then atoms := atoms.push s
    if cap ≤ atoms.size then break
  pure (atoms.toList.take cap |>.toArray)

/-- Match one `∀`-hypothesis against the pool. Runs inside
`forallTelescope` so telescope fvars stay in scope; returns only ground
argument arrays (no telescope fvars leak out). -/
def matchHyp (h : ForallHyp) (pool : Array Expr)
    (atoms : Array Expr) (uf : UnionFind) : TacticM (List (Array Expr)) := do
  forallTelescope h.ty fun xs body => do
    if xs.isEmpty then return []
    let trigs := (extractTriggers xs body).take 8
    let mut out : List (Array Expr) := []
    for t in trigs do
      for g in pool do
        if 6 ≤ out.length then return out
        match matchMod atoms uf xs t g #[] with
        | none => pure ()
        | some subst =>
          match xs.mapM fun x => subst.find? fun p => p.1 == x with
          | none => pure ()
          | some pairs =>
            let args := pairs.map Prod.snd
            let mut ok := true
            for (x, a) in xs.zip args do
              unless ← isDefEq (← inferType a) (← inferType x) do
                ok := false
            if ok then out := args :: out else pure ()
    pure out

/-- Attempt one instance assertion (`hyp args`); true on success.
Ill-typed candidates fail kernel checking and return false. -/
def tryAssert (fproof : Expr) (args : Array Expr)
    (seen : IO.Ref (Array Expr)) (ctr : IO.Ref Nat) : TacticM Bool := do
  try
    let prf := mkAppN fproof args
    let ty ← inferType prf
    if (← seen.get).any (· == ty) then return false
    let mvar ← getMainGoal
    let c ← ctr.get
    let (_, mvar') ← mvar.note
      (Name.mkStr1 s!"lynth_inst_{c}") prf (some ty)
    replaceMainGoal [mvar']
    seen.set ((← seen.get).push ty)
    ctr.set (c + 1)
    pure true
  catch _ => pure false

/-- E-matching round: instantiate all `∀`-hyps (capped), assert proven
instances, return the count. Always yields (never closes the goal). -/
def instantiate (maxInst : Nat := 6) : TacticM Nat := do
  let hyps ← collectForalls
  if hyps.isEmpty then return 0
  let pool ← groundPool 64
  if pool.isEmpty then return 0
  -- EUF congruence classes over context equalities (bounded inside)
  let edges0 ← Lynth.Euf.Procedure.collectEdges
  let seeds := pool.toList ++
    (hyps.toList.flatMap fun h =>
      Lynth.Euf.Procedure.collectSubterms h.ty)
  let edges ← Lynth.Euf.Procedure.congrClose edges0 seeds
  let (atoms, _) := Lynth.Euf.Procedure.buildGraph edges seeds
  let mut uf := UnionFind.mk' atoms.size
  for (a, b, _) in edges do
    uf := uf.union
      (Lynth.Euf.Procedure.idxOf atoms a) (Lynth.Euf.Procedure.idxOf atoms b)
  let mut count := 0
  let seen ← IO.mkRef (α := Array Expr) #[]
  let ctr ← IO.mkRef 0
  for h in hyps.toList.take 8 do
    if maxInst ≤ count then break
    try
      let argss ← matchHyp h pool atoms uf
      for args in argss do
        if maxInst ≤ count then break
        if ← tryAssert h.proof args seen ctr then
          count := count + 1
    catch _ => pure ()
  pure count

/-- Run the procedure: enrich context, always yield. -/
def run : TacticM ProcedureOutcome := do
  let n ← instantiate 6
  if n > 0 then logInfo m!"[lynth:quant] asserted {n} instances"
  return .failure []

end Lynth.Quant.Procedure
