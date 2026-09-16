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

/-- Split `e` as `(lhs, rhs)` if it is a disequality `lhs ≠ rhs`
(either `Ne` or `¬(_ = _)`). -/
def asNe (e : Expr) : MetaM (Option (Expr × Expr)) := do
  let e ← whnf e
  match e with
  | .app (.app (.const ``Ne _) lhs) rhs => pure (some (lhs, rhs))
  | .app (.const ``Not _) a => asEq a
  | .forallE _ d b _ =>
    if b.hasLooseBVars then pure none
    else asEq d
  | _ => pure none

/-- Proof term of a local hypothesis declaration. -/
def hypProof : LocalDecl → Expr
  | .ldecl _ fvarId _ _ _ _ _ => .fvar fvarId
  | .cdecl _ fvarId _ _ _ _ => .fvar fvarId

/-- Collect `(lhs, rhs, proof)` from `≠`-typed local hypotheses. -/
def collectNe : TacticM (Array (Expr × Expr × Expr)) := do
  let mut nes := #[]
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      match ← asNe decl.type with
      | some (lhs, rhs) => nes := nes.push (lhs, rhs, hypProof decl)
      | none => pure ()
  pure nes

/-- Collect `(lhs, rhs, proof)` edges from `Eq`-typed local hypotheses.
Skips auxiliary declarations (e.g. the `_example` self-reference Lean
parks in context, which `assumption` also ignores): using it as an edge
would "prove" a goal from itself. -/
def collectEdges : TacticM (Array (Expr × Expr × Expr)) := do
  let mut edges := #[]
  for decl in ← getLCtx do
    if (decl.kind == .default) then
      match ← asEq decl.type with
      | some (lhs, rhs) => edges := edges.push (lhs, rhs, hypProof decl)
      | none => pure ()
  pure edges

/-- All subterms of `e` (including `e`), for congruence candidate mining. -/
def collectSubterms : Expr → List Expr
  | e@(.app f a) => e :: (collectSubterms f ++ collectSubterms a)
  | e@(.mdata _ b) => e :: collectSubterms b
  | e@(.proj _ _ b) => e :: collectSubterms b
  | e@(.lam _ _ b _) => e :: collectSubterms b
  | e@(.forallE _ t b _) => e :: (collectSubterms t ++ collectSubterms b)
  | e@(.letE _ t v b _) => e :: (collectSubterms t ++ collectSubterms v ++ collectSubterms b)
  | e => [e]

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

/-- Node id lookup (all queried exprs are pre-registered). -/
def idxOf (atoms : Array Expr) (e : Expr) : Nat :=
  (atoms.findIdx? (· == e)).getD 0

/-- Register `e` in the atom table if absent. -/
def reg (atoms : Array Expr) (e : Expr) : Array Expr :=
  if (atoms.findIdx? (· == e)).isNone then atoms.push e else atoms

/-- Atom table + adjacency from edges plus goal sides (including every
function/argument subterm, so congruence candidates are nodes). -/
def buildGraph (edges : Array (Expr × Expr × Expr)) (seeds : List Expr) :
    Array Expr × Adj :=
  Id.run do
  let mut atoms : Array Expr := #[]
  for (a, b, _) in edges do
    for s in collectSubterms a ++ collectSubterms b do
      atoms := reg atoms s
  for e in seeds do
    for s in collectSubterms e do
      atoms := reg atoms s
  let n := atoms.size
  let mut adj : Adj := Array.replicate n #[]
  for (a, b, prf) in edges do
    let ia := idxOf atoms a
    let ib := idxOf atoms b
    adj := adj.set! ia (adj[ia]! ++ [(ib, prf, true)])
    adj := adj.set! ib (adj[ib]! ++ [(ia, prf, false)])
  (atoms, adj)

/-- Deduplicate a list of exprs (syntactic `==`). -/
def dedup : List Expr → List Expr
  | [] => []
  | e :: rest => if rest.any (· == e) then dedup rest else e :: dedup rest

/-- Congruence-closure fixpoint over `edges`: returns the closed edge
set with `congr` proof terms. Fuel-bounded. -/
def congrClose (edges0 : Array (Expr × Expr × Expr)) (seeds : List Expr) :
    TacticM (Array (Expr × Expr × Expr)) := do
  let mut edges := edges0
  let mut rounds := 8
  let mut changed := true
  while changed && rounds > 0 do
    changed := false
    rounds := rounds - 1
    let (atoms, adj) := buildGraph edges seeds
    let subs := dedup ((seeds.flatMap collectSubterms) ++
      (edges.toList.flatMap fun (a, b, _) => collectSubterms a ++ collectSubterms b))
    let apps := subs.filter fun e => match e with
      | .app _ _ => true
      | _ => false
    for u in apps do
      for v in apps do
        if u != v then
          match (u, v) with
          | (.app f1 a1, .app f2 a2) =>
            let i1 := idxOf atoms f1; let j1 := idxOf atoms a1
            let i2 := idxOf atoms f2; let j2 := idxOf atoms a2
            let iu := idxOf atoms u; let iv := idxOf atoms v
            match (bfsPath adj i1 i2, bfsPath adj j1 j2, bfsPath adj iu iv) with
            | (some pf, some pa, none) =>
              try
                let hf ← buildProof f1 pf
                let ha ← buildProof a1 pa
                let h ← mkAppM ``congr #[hf, ha]
                edges := edges.push (u, v, h)
                changed := true
              catch _ => pure ()
            | _ => pure ()
          | _ => pure ()
  pure edges

/-- Share derived equalities with the rest of the pipeline: assert every
newly reachable `u = v` (up to `maxFacts`) as a hypothesis with its
proof, so later procedures can use it. This is lynth's variable-sharing
mechanism: explanations flow as proven equality facts in context.
Returns the number of facts asserted. -/
def shareDerived (maxFacts : Nat := 8) : TacticM Nat := do
  let edges0 ← collectEdges
  if edges0.isEmpty then return 0
  -- scope atoms: edge endpoints (+ goal sides when the goal is an `Eq`)
  let goal ← getMainTarget
  let seeds : List Expr :=
    match ← asEq goal with
    | some (l, r) => [l, r]
    | none =>
      match edges0[0]? with
      | some (a, b, _) => [a, b]
      | none => []
  let edges ← congrClose edges0 seeds
  let (atoms, adj) := buildGraph edges seeds
  let m := atoms.size
  let mut count := 0
  let mut seen : Array (Nat × Nat) := #[]
  for i in List.range m do
    for j in List.range m do
      if count < maxFacts && i != j then
        -- skip pairs already directly linked by a hypothesis edge
        let linked := edges.any fun (a, b, _) =>
          (idxOf atoms a == i && idxOf atoms b == j) ||
          (idxOf atoms a == j && idxOf atoms b == i)
        if !linked && !(seen.any fun (x, y) => (x == i && y == j) || (x == j && y == i)) then
          match bfsPath adj i j with
          | some path =>
            try
              let prf ← buildProof atoms[i]! path
              let ty ← mkAppM ``Eq #[atoms[i]!, atoms[j]!]
              let mvar ← getMainGoal
              let (_, mvar') ← mvar.note (Name.mkStr1 s!"lynth_eq_{i}_{j}") prf (some ty)
              replaceMainGoal [mvar']
              seen := seen.push (i, j)
              count := count + 1
            catch _ => pure ()
          | none => pure ()
  if count > 0 then
    logInfo m!"[lynth:euf] shared {count} derived equalities"
  pure count

/-- Reachability close for `lhs = rhs` over current hypotheses. -/
def closeEq (lhs rhs : Expr) : TacticM Bool := do
  let edges0 ← collectEdges
  if edges0.isEmpty then return false
  let edges ← congrClose edges0 [lhs, rhs]
  let (atoms, adj) := buildGraph edges [lhs, rhs]
  match bfsPath adj (idxOf atoms lhs) (idxOf atoms rhs) with
  | none => pure false
  | some path =>
    try
      let prf ← buildProof lhs path
      let mvar ← getMainGoal
      mvar.assign prf
      replaceMainGoal []
      pure true
    catch _ => pure false

/-- Close a `False` goal by contradicting a `≠` hypothesis: if closure
connects some hyp's `l ~ r`, `exact (neHyp proof)`. Sound: the equality
proof may use every hypothesis in context, including intro'd ones. -/
def closeFalse : TacticM Bool := do
  let nes ← collectNe
  if nes.isEmpty then return false
  let edges0 ← collectEdges
  let seeds := nes.toList.flatMap fun (l, r, _) => [l, r]
  let edges ← congrClose edges0 seeds
  let (atoms, adj) := buildGraph edges seeds
  for (l, r, neprf) in nes do
    match bfsPath adj (idxOf atoms l) (idxOf atoms r) with
    | none => pure ()
    | some path =>
      try
        let prf ← buildProof l path
        let mvar ← getMainGoal
        mvar.assign (mkApp neprf prf)
        replaceMainGoal []
        return true
      catch _ => pure ()
  pure false

/-- Try to close an `Eq` goal by equality closure, or a `Ne`/`False` goal
by disequality-driven closure. On failure, shares derived equalities
into context before yielding to the next procedure. -/
def run : TacticM ProcedureOutcome := do
  let snapshot ← saveState
  let goal ← getMainTarget
  match ← asEq goal with
  | some (lhs, rhs) =>
    if lhs == rhs then
      let rfl ← `(tactic| rfl)
      evalTactic rfl
      if (← getUnsolvedGoals).isEmpty then return .success
      else
        restoreState snapshot
        return .failure []
    else match ← closeEq lhs rhs with
      | true => return .success
      | false =>
        logInfo "[lynth:euf] no equality path; sharing derived facts"
        let _ ← shareDerived
        return .failure []
  | none =>
    -- Disequality-driven close: intro the equation (if the goal is `Ne`),
    -- then contradict a `≠` hypothesis by closure. Also handles a bare
    -- `False` goal directly.
    match ← asNe goal with
    | none =>
      if (← whnfR goal).isConstOf ``False then
        if ← closeFalse then return .success else return .failure []
      else return .failure []
    | some _ =>
      let introStx ← `(tactic| intro h_euf_ne)
      try evalTactic introStx catch _ => return .failure []
      -- re-focus: `intro` changes the main goal's context, refresh it
      withMainContext do
        if ← closeFalse then return .success
        else
          restoreState snapshot
          return .failure []

end Lynth.Euf.Procedure
