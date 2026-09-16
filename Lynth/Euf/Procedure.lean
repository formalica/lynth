-- EUF procedure (part 1): close `a = b` goals from `Eq` hypotheses
-- by transitivity/symmetry chains, rebuilding kernel-checked proofs.
--
-- Each `Eq` hypothesis becomes a graph edge carrying its proof term;
-- BFS finds a path between the goal's sides and folds it with
-- `Eq.trans`/`Eq.symm`. Failure returns an empty explanation (derived
-- equalities as shareable `Fact`s land with the CDCL(T) loop).
import Lean
import Lynth.Procedure

namespace Lynth.Euf.Procedure

open Lean Elab Tactic Meta

/-- Split `e` as `lhs = rhs` if it is an `Eq` application. -/
def asEq (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfR e
  match e with
  | .app (.app (.app (.const ``Eq _) _) lhs) rhs => pure (some (lhs, rhs))
  | _ => pure none

/-- Proof term of a local hypothesis declaration. -/
def hypProof : LocalDecl → Expr
  | .ldecl _ fvarId _ _ _ _ _ => .fvar fvarId
  | .cdecl _ fvarId _ _ _ _ => .fvar fvarId

/-- Collect `(lhs, rhs, proof)` edges from `Eq`-typed local hypotheses. -/
def collectEdges : TacticM (Array (Expr × Expr × Expr)) := do
  let mut edges := #[]
  for decl in ← getLCtx do
    match ← asEq decl.type with
    | some (lhs, rhs) => edges := edges.push (lhs, rhs, hypProof decl)
    | none => pure ()
  pure edges

/-- Adjacency: for each node, `(neighbor, edgeProof, forward)` steps. -/
abbrev Adj := Array (Array (Nat × Expr × Bool))

/-- One BFS level expansion. -/
def expandLevel (adj : Adj) (dst : Nat)
    (frontier : List Nat) (prev : Array (Option (Nat × Expr × Bool))) :
    Array (Option (Nat × Expr × Bool)) × List Nat × Bool :=
  frontier.foldl (fun (prev', next, found) cur =>
    (adj[cur]!).foldl (fun (prev'', next', found') (nxt, prf, fwd) =>
      if (prev''[nxt]!).isSome then (prev'', next', found')
      else
        (prev''.set! nxt (some (cur, prf, fwd)),
         if nxt == dst then next' else next' ++ [nxt],
         found' || nxt == dst)
    ) (prev', next, found)
  ) (prev, [], false)

/-- Fuel-bounded BFS. Returns the predecessor table on success. -/
def bfsLoop (adj : Adj) (dst : Nat) : List Nat →
    Array (Option (Nat × Expr × Bool)) → Nat →
    Option (Array (Option (Nat × Expr × Bool)))
  | _, _prev, 0 => none
  | [], _, _ => none
  | frontier, prev, fuel + 1 =>
    let (prev', next, found) := expandLevel adj dst frontier prev
    if found then some prev' else bfsLoop adj dst next prev' fuel

/-- Rebuild the edge path `src → dst` from a predecessor table. -/
def rebuildPath (src dst : Nat)
    (prev : Array (Option (Nat × Expr × Bool))) (fuel : Nat) :
    Option (List (Expr × Bool)) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    if dst == src then some []
    else match prev[dst]! with
      | none => none
      | some (p, prf, fwd) =>
        match rebuildPath src p prev fuel with
        | none => none
        | some rest => some (rest ++ [(prf, fwd)])

/-- BFS path from `src` to `dst` over undirected edges.
Each step is `(edgeProof, forward : Bool)` where `forward`
means the edge runs in its stated direction. -/
def bfsPath (adj : Adj) (src dst : Nat) : Option (List (Expr × Bool)) := do
  if src == dst then return []
  let n := adj.size
  let init : Array (Option (Nat × Expr × Bool)) :=
    Array.replicate n none |>.set! src (some (src, Expr.const ``True [], true))
  let prev ← bfsLoop adj dst [src] init (n * n + 1)
  rebuildPath src dst prev (n + 1)

/-- Fold a path into a proof term: `Eq.trans` chains with `Eq.symm`
for backward edges, starting from `Eq.refl lhs`. -/
def buildProof (lhs : Expr) (path : List (Expr × Bool)) : MetaM Expr := do
  let mut cur : Expr ← mkAppM ``Eq.refl #[lhs]
  for (prf, fwd) in path do
    let step ← if fwd then pure prf else mkAppM ``Eq.symm #[prf]
    cur ← mkAppM ``Eq.trans #[cur, step]
  pure cur

/-- Try to close an `Eq` goal by equality closure. -/
def run : TacticM ProcedureOutcome := do
  let goal ← getMainTarget
  let some (lhs, rhs) ← asEq goal | return .failure []
  if lhs == rhs then
    let rfl ← `(tactic| rfl)
    evalTactic rfl
    if (← getUnsolvedGoals).isEmpty then return .success
    else return .failure []
  let edges ← collectEdges
  if edges.isEmpty then return .failure []
  -- atom table over all edge endpoints + goal sides
  let mut atoms : Array Expr := #[]
  let idxOf : Array Expr → Expr → Nat :=
    fun arr e => (arr.findIdx? (· == e)).getD 0
  for (a, b, _) in edges do
    if (atoms.findIdx? (· == a)).isNone then atoms := atoms.push a
    if (atoms.findIdx? (· == b)).isNone then atoms := atoms.push b
  if (atoms.findIdx? (· == lhs)).isNone then atoms := atoms.push lhs
  if (atoms.findIdx? (· == rhs)).isNone then atoms := atoms.push rhs
  let n := atoms.size
  let mut adj : Adj := Array.replicate n #[]
  for (a, b, prf) in edges do
    let ia := idxOf atoms a
    let ib := idxOf atoms b
    adj := adj.set! ia (adj[ia]! ++ [(ib, prf, true)])
    adj := adj.set! ib (adj[ib]! ++ [(ia, prf, false)])
  let s := idxOf atoms lhs
  let t := idxOf atoms rhs
  match bfsPath adj s t with
  | none =>
    logInfo "[lynth:euf] no equality path"
    return .failure []
  | some path =>
    try
      let prf ← buildProof lhs path
      let mvar ← getMainGoal
      mvar.assign prf
      replaceMainGoal []
      return .success
    catch _ =>
      return .failure []

end Lynth.Euf.Procedure
