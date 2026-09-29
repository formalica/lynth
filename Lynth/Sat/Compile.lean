import Lean
import Lynth.Sat.Differ
import Lynth.Sat.Verified

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
open Lynth.Sat.Gates
open Lynth.Sat.FinVal
open Lynth.Sat.Differ

/-- Fragment kinds in v1: guarded inequality / equality /
injectivity / required-guard over single-level `Fin` outputs.
Multi-index outputs and arithmetic arrive as later fragments without
touching this code. -/
inductive FragKind
  | ne
  | eq
  | inj
  | req
  deriving BEq, Repr, DecidableEq

/-- One classified constraint family: shared bound `n`, value count
`k`, and a closed guard. Guard contract by kind: `ne`/`eq` take
`input → Fin n → Fin n → Bool`; `req` takes
`input → Fin n → Fin k → Bool`; `inj` ignores it. -/
structure Frag where
  kind : FragKind
  n : Nat
  k : Nat
  guard : Expr

/-- N-ary conjunction split (right-nested `And` chains). -/
def splitConj : Expr → List Expr
  | .app (.app (.const ``And _) a) b => a :: splitConj b
  | e => [e]

/-- Guarded-difference family over all index pairs. -/
def neFamCNF (I : Type) (n k : Nat)
    (guard : I → Fin n → Fin n → Bool) (input : I) : CNF :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      condDiffPair k i.val j.val (guard input i j)

/-- Fragment soundness (inequality): held families decode to
guard-respecting different values. -/
theorem neFam_sound (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin n → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin n,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (neFamCNF I n k guard input) m = true) :
    ∀ i j : Fin n, guard input i j = true →
      decodeVal n k hk m i ≠ decodeVal n k hk m j := by
  intro i j hg
  -- fire the family at `(i, j)`: rewrite by guard truth, then lift
  -- every clause from the full family (all first-order, no heavy
  -- unification)
  have hfamIJ : condDiffPair k i.val j.val (guard input i j)
      = diffCNF k [(i.val, j.val)] := by
    simp [condDiffPair, condClauses, hg]
  have hpiece : checkSat (diffCNF k [(i.val, j.val)]) m = true := by
    rw [← hfamIJ]
    apply checkSat_of_all_single
    intro cl hc
    rw [hfamIJ] at hc
    obtain ⟨p, hpm, hclm⟩ := List.mem_flatMap.mp hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpm
    subst hpm
    obtain ⟨c, hcm, hfc⟩ := List.mem_map.mp hclm
    subst hfc
    apply checkSat_mem m _ _ _ hfam
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_finRange i, ?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨j, List.mem_finRange j, ?_⟩
    show diffClause k i.val j.val c.val ∈
      condDiffPair k i.val j.val (guard input i j)
    rw [hfamIJ]
    apply List.mem_flatMap.mpr
    refine ⟨(i.val, j.val), List.mem_cons_self, ?_⟩
    exact List.mem_map.mpr ⟨c, hcm, rfl⟩
  have hper : ∀ c : Fin k,
      checkSat [diffClause k i.val j.val c.val] m = true := by
    intro c
    have hmem : diffClause k i.val j.val c.val ∈ diffCNF k [(i.val, j.val)] := by
      unfold diffCNF
      exact List.mem_flatMap.mpr ⟨(i.val, j.val), List.mem_cons_self,
        List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩⟩
    exact checkSat_mem m _ _ hmem hpiece
  exact diff_sound_decode n k hk m i j (hrows i) (hrows j) hper

/-- Fragment completeness (inequality): valid functions satisfy. -/
theorem neFam_complete (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin n → Bool) (input : I)
    (f : Fin n → Fin k)
    (hvalid : ∀ i j : Fin n, guard input i j = true → f i ≠ f j) :
    checkSat (neFamCNF I n k guard input) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro i him
  apply checkSat_flatMap
  intro j hjm
  by_cases hg : guard input i j = true
  · have h2 : checkSat (diffCNF k [(i.val, j.val)]) (modelOf n k f)
        = true :=
      diffCNF_complete n k hk f i j (hvalid i j hg)
    have h3 : checkSat (condDiffPair k i.val j.val (guard input i j))
        (modelOf n k f) = true :=
      condClauses_of_true _ _ _ hg h2
    simpa [condDiffPair] using h3
  · have h0 : condDiffPair k i.val j.val (guard input i j) = [] := by
      simp [condDiffPair, condClauses, hg]
    change checkSat (condDiffPair k i.val j.val (guard input i j))
      (modelOf n k f) = true
    rw [h0]
    rfl

/-- Guarded-equality family over all index pairs. -/
def eqFamCNF (I : Type) (n k : Nat)
    (guard : I → Fin n → Fin n → Bool) (input : I) : CNF :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      condEqPair k i.val j.val (guard input i j)

/-- Fired equality piece: from a held family with true guard, one
value-pair holds. All first-order and concrete. -/
theorem eqFam_piece (I : Type) (n k : Nat)
    (guard : I → Fin n → Fin n → Bool) (input : I) (m : Assignment)
    (i j : Fin n) (c : Fin k)
    (hg : guard input i j = true)
    (h : checkSat (eqFamCNF I n k guard input) m = true) :
    checkSat (eqClausePair k i.val j.val c.val) m = true := by
  have hfamIJ : condEqPair k i.val j.val (guard input i j)
      = eqCNF k [(i.val, j.val)] := by
    simp [condEqPair, condClauses, hg]
  apply checkSat_of_all_single
  intro cl hc
  -- rebuild into the full family through the fired piece
  apply checkSat_mem m _ _ _ h
  apply List.mem_flatMap.mpr
  refine ⟨i, List.mem_finRange i, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨j, List.mem_finRange j, ?_⟩
  change cl ∈ condEqPair k i.val j.val (guard input i j)
  rw [hfamIJ]
  apply List.mem_flatMap.mpr
  refine ⟨(i.val, j.val), List.mem_cons_self, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨c, List.mem_finRange c, ?_⟩
  simpa [eqClausePair] using hc

/-- Fragment soundness (equality). -/
theorem eqFam_sound (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin n → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin n,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (eqFamCNF I n k guard input) m = true) :
    ∀ i j : Fin n, guard input i j = true →
      decodeVal n k hk m i = decodeVal n k hk m j := by
  intro i j hg
  have hper : ∀ c : Fin k,
      checkSat (eqClausePair k i.val j.val c.val) m = true := by
    intro c
    exact eqFam_piece I n k guard input m i j c hg hfam
  exact eq_sound_decode n k hk m i j (hrows i) (hrows j) hper

/-- Fragment completeness (equality). -/
theorem eqFam_complete (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin n → Bool) (input : I)
    (f : Fin n → Fin k)
    (hvalid : ∀ i j : Fin n, guard input i j = true → f i = f j) :
    checkSat (eqFamCNF I n k guard input) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro i him
  apply checkSat_flatMap
  intro j hjm
  by_cases hg : guard input i j = true
  · have h2 : checkSat (eqCNF k [(i.val, j.val)]) (modelOf n k f)
        = true :=
      eqCNF_complete n k hk f i j (hvalid i j hg)
    have h3 : checkSat (condEqPair k i.val j.val (guard input i j))
        (modelOf n k f) = true :=
      condClauses_of_true _ _ _ hg h2
    simpa [condEqPair] using h3
  · have h0 : condEqPair k i.val j.val (guard input i j) = [] := by
      simp [condEqPair, condClauses, hg]
    change checkSat (condEqPair k i.val j.val (guard input i j))
      (modelOf n k f) = true
    rw [h0]
    rfl

/-- Injectivity family: complete pairwise difference. -/
def injFamCNF (n k : Nat) : CNF :=
  (List.finRange n).flatMap fun i =>
    (List.finRange n).flatMap fun j =>
      condDiffPair k i.val j.val (decide (i ≠ j))

/-- Fragment soundness (injectivity). -/
theorem injFam_sound (n k : Nat) (hk : 0 < k)
    (m : Assignment)
    (hrows : ∀ v : Fin n,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (injFamCNF n k) m = true) :
    Function.Injective (fun v => decodeVal n k hk m v) := by
  intro a b hab
  by_cases heq : a = b
  · exact heq
  · have hne : a ≠ b := heq
    have hg : decide (a ≠ b) = true := decide_eq_true hne
    have hfamIJ : condDiffPair k a.val b.val (decide (a ≠ b))
        = diffCNF k [(a.val, b.val)] := by
      simp [condDiffPair, condClauses, hg]
    have hpiece : checkSat (diffCNF k [(a.val, b.val)]) m = true := by
      rw [← hfamIJ]
      apply checkSat_of_all_single
      intro cl hc
      rw [hfamIJ] at hc
      obtain ⟨p, hpm, hclm⟩ := List.mem_flatMap.mp hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hpm
      subst hpm
      obtain ⟨c, hcm, hfc⟩ := List.mem_map.mp hclm
      subst hfc
      apply checkSat_mem m _ _ _ hfam
      apply List.mem_flatMap.mpr
      refine ⟨a, List.mem_finRange a, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨b, List.mem_finRange b, ?_⟩
      show diffClause k a.val b.val c.val ∈
        condDiffPair k a.val b.val (decide (a ≠ b))
      rw [hfamIJ]
      apply List.mem_flatMap.mpr
      refine ⟨(a.val, b.val), List.mem_cons_self, ?_⟩
      exact List.mem_map.mpr ⟨c, hcm, rfl⟩
    have hper : ∀ c : Fin k,
        checkSat [diffClause k a.val b.val c.val] m = true := by
      intro c
      have hmem : diffClause k a.val b.val c.val ∈ diffCNF k [(a.val, b.val)] := by
        unfold diffCNF
        exact List.mem_flatMap.mpr ⟨(a.val, b.val), List.mem_cons_self,
          List.mem_map.mpr ⟨c, List.mem_finRange c, rfl⟩⟩
      exact checkSat_mem m _ _ hmem hpiece
    have hdn := diff_sound_decode n k hk m a b (hrows a) (hrows b) hper
    exact absurd hab hdn

/-- Fragment completeness (injectivity). -/
theorem injFam_complete (n k : Nat) (hk : 0 < k)
    (f : Fin n → Fin k) (hinj : Function.Injective f) :
    checkSat (injFamCNF n k) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro i him
  apply checkSat_flatMap
  intro j hjm
  by_cases heq : i = j
  · have hgf : decide (i ≠ j) = false := by simp [heq]
    have h0 : condDiffPair k i.val j.val (decide (i ≠ j)) = [] := by
      simp [condDiffPair, condClauses, hgf]
    change checkSat (condDiffPair k i.val j.val (decide (i ≠ j)))
      (modelOf n k f) = true
    rw [h0]
    rfl
  · have hne : i ≠ j := heq
    have hg : decide (i ≠ j) = true := decide_eq_true hne
    have h2 : checkSat (diffCNF k [(i.val, j.val)]) (modelOf n k f)
        = true :=
      diffCNF_complete n k hk f i j (fun h => hne (hinj h))
    have h3 : checkSat (condDiffPair k i.val j.val (decide (i ≠ j)))
        (modelOf n k f) = true :=
      condClauses_of_true _ _ _ hg h2
    simpa [condDiffPair] using h3

/-- Required-guard family: forbid each value unless its guard holds. -/
def reqFamCNF (I : Type) (n k : Nat)
    (guard : I → Fin n → Fin k → Bool) (input : I) : CNF :=
  (List.finRange n).flatMap fun i =>
    (List.finRange k).flatMap fun v =>
      condUnitNeg k i.val v.val (guard input i v)

/-- Fragment soundness (required guard). -/
theorem reqFam_sound (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin k → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin n,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (reqFamCNF I n k guard input) m = true) :
    ∀ i : Fin n, guard input i (decodeVal n k hk m i) = true := by
  intro i
  -- every value-piece at cell `i` holds (casing on its guard)
  have hper : ∀ c : Fin k, checkSat
      (condUnitNeg k i.val c.val (guard input i c)) m = true := by
    intro c
    by_cases hg : guard input i c = true
    · have hempty : condUnitNeg k i.val c.val (guard input i c) = [] := by
        simp [condUnitNeg, condClauses, hg]
      rw [hempty]
      rfl
    · have hguardF : guard input i c = false :=
        Bool.eq_false_of_ne_true hg
      have hunit : condUnitNeg k i.val c.val (guard input i c)
          = [[-Int.ofNat (idxVar k i.val c.val)]] := by
        simp [condUnitNeg, condClauses, hguardF]
      apply checkSat_of_all_single
      intro cl hc
      rw [hunit] at hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      subst hc
      apply checkSat_mem m _ _ _ hfam
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨c, List.mem_finRange c, ?_⟩
      change [-Int.ofNat (idxVar k i.val c.val)] ∈
        condUnitNeg k i.val c.val (guard input i c)
      rw [hunit]
      exact List.mem_cons_self
  exact unitNeg_sound n k (guard input) hk m i (hrows i) hper

/-- Fragment completeness (required guard). -/
theorem reqFam_complete (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin k → Bool) (input : I)
    (f : Fin n → Fin k)
    (hvalid : ∀ i : Fin n, guard input i (f i) = true) :
    checkSat (reqFamCNF I n k guard input) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro i him
  apply checkSat_flatMap
  intro v hvm
  by_cases hg : guard input i v = true
  · have hempty : condUnitNeg k i.val v.val (guard input i v) = [] := by
      simp [condUnitNeg, condClauses, hg]
    have hgoal : checkSat
        (condUnitNeg k i.val v.val (guard input i v))
        (modelOf n k f) = true := by
      rw [hempty]
      rfl
    simpa using hgoal
  · -- `[¬x]` with `x` false under the model
    have hne : f i ≠ v := by
      intro hcon
      exact hg (hcon ▸ hvalid i)
    have hnb : decide (f i = v) = false := by simp [hne]
    have hev : evalLit (modelOf n k f)
        (-Int.ofNat (idxVar k i.val v.val)) = some true := by
      rw [evalLit_neg]
      have he : evalLit (modelOf n k f)
          ((idxVar k i.val v.val : Nat) : Lit)
          = some (decide (f i = v)) := by
        simpa using modelOf_eval n k hk f i v
      simp [he, hnb]
    have hgoal : checkSat
        (condUnitNeg k i.val v.val (guard input i v))
        (modelOf n k f) = true := by
      have hguardF : guard input i v = false :=
        Bool.eq_false_of_ne_true hg
      have hunit : condUnitNeg k i.val v.val (guard input i v)
          = [[-Int.ofNat (idxVar k i.val v.val)]] := by
        simp [condUnitNeg, condClauses, hguardF]
      rw [hunit]
      exact (checkSat_single _ _).mpr hev
    simpa using hgoal

/-- Match `Function.Injective f` with `f` the output fvar. -/
def matchInj (body outFv : Expr) : MetaM (Option Expr) := do
  let bR ← whnf body
  match bR.getAppFn with
  | .const ``Function.Injective _ =>
    let args := bR.getAppArgs
    if args.size != 1 then pure none
    else
      match args[0]! with
      | .fvar fid =>
        if fid != outFv.fvarId! then pure none
        else pure (some bR)
      | _ => pure none
  | _ => pure none

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
    MetaM (Option (Expr × Expr × Expr × Bool)) := do
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
            -- codomain: `lhs ≠ rhs` (`Ne`-applied), `lhs = rhs`
            -- (`Eq`-applied), or unfolded-`Not` fallback.
            -- NOTE: `whnf` would unfold `Ne` away, so match the
            -- raw head first.
            match cod.getAppFn with
            | .const ``Ne _ =>
              let cargs := cod.getAppArgs
              if cargs.size != 3 then pure none
              else pure (some (guardApp, cargs[1]!, cargs[2]!, true))
            | .const ``Eq _ =>
              let cargs := cod.getAppArgs
              if cargs.size != 3 then pure none
              else pure (some (guardApp, cargs[1]!, cargs[2]!, false))
            | _ =>
              let codR ← whnf cod
              match codR with
              | .app (.const ``Not _) eqProp =>
                let eqR ← whnf eqProp
                match eqR.getAppFn with
                | .const ``Eq _ =>
                  let eargs := eqR.getAppArgs
                  if eargs.size != 3 then pure none
                  else pure (some (guardApp, eargs[1]!, eargs[2]!, true))
                | _ => pure none
              | _ => pure none
          | _ =>
            pure none
      | _ =>
        pure none
  | _ => pure none

/-- Find an output application `c x` (head `c`, any argument) in `e`. -/
def findOutApp (e : Expr) (c : FVarId) : Option Expr :=
  e.find? fun s => match s with
    | .app (.fvar fid) _ => fid == c
    | _ => false

/-- `Fin n` as a type term from a literal bound. -/
def finTyLit (n : Nat) : Expr :=
  mkApp (mkConst ``Fin []) (mkNatLit n)

/-- `Fin.val` projection. -/
def finValOf (e : Expr) : MetaM Expr :=
  mkAppM ``Fin.val #[e]

/-- `List.finRange n` term. -/
def finRangeLit (n : Nat) : MetaM Expr := do
  pure (mkApp (mkConst ``List.finRange []) (mkNatLit n))

/-- `List.flatMap` application (`f` first). -/
def flatMapApp (l f : Expr) : MetaM Expr :=
  mkAppM ``List.flatMap #[f, l]

/-- `List.append` application. -/
def appendApp (a b : Expr) : MetaM Expr :=
  mkAppM ``List.append #[a, b]

/-- `0 < k` proof for literal `k` (closed decidable prop). -/
def zeroLtLit (k : Nat) : MetaM Expr := do
  let p ← mkAppM ``LT.lt #[mkNatLit 0, mkNatLit k]
  mkDecideProof p

/-- Build one fragment family's CNF. Index binders are created fresh;
`gin` is the input fvar. -/
def mkFamBody (fr : Frag) (gin : Expr) (n k : Nat) : MetaM Expr := do
  let kk := mkNatLit k
  match fr.kind with
  | .inj =>
    -- complete difference with a decidable diagonal guard
    withLocalDeclD `i (finTyLit n) fun i =>
    withLocalDeclD `j (finTyLit n) fun j => do
      let ne ← mkAppM ``Ne #[i, j]
      let gd ← mkDecide ne
      let piece ← mkAppM ``Lynth.Sat.Differ.condDiffPair
        #[kk, ← finValOf i, ← finValOf j, gd]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit n
      flatMapApp ri lamI
  | .req =>
    withLocalDeclD `i (finTyLit n) fun i =>
    withLocalDeclD `v (finTyLit k) fun v => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condUnitNeg
        #[kk, ← finValOf i, ← finValOf v,
          mkAppN fr.guard #[gin, i, v]]
      let lamV ← mkLambdaFVars #[v] piece
      let rv ← finRangeLit k
      let inner ← flatMapApp rv lamV
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit n
      flatMapApp ri lamI
  | .ne =>
    withLocalDeclD `i (finTyLit n) fun i =>
    withLocalDeclD `j (finTyLit n) fun j => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condDiffPair
        #[kk, ← finValOf i, ← finValOf j,
          mkAppN fr.guard #[gin, i, j]]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit n
      flatMapApp ri lamI
  | .eq =>
    withLocalDeclD `i (finTyLit n) fun i =>
    withLocalDeclD `j (finTyLit n) fun j => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condEqPair
        #[kk, ← finValOf i, ← finValOf j,
          mkAppN fr.guard #[gin, i, j]]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit n
      flatMapApp ri lamI

/-- Right-nested append chain over components (shared by encoder
and assembler so terms match syntactically). -/
def appendChain : List Expr → MetaM Expr
  | [] => throwError "appendChain: empty"
  | [c] => pure c
  | c :: cs => do
    let rest ← appendChain cs
    appendApp c rest

/-- Encoder body plus per-family CNF terms (all mentioning `gin`):
`(body, [fam_0, ..., fam_{m-1}, cells])` with
`body` the `appendChain` of that list, matching `liftMem` indexing
(families `0..m-1`, cells at `m`). -/
def mkEncodeBody (gin : Expr) (frags : List Frag) (n k : Nat) :
    MetaM (Expr × List Expr) := do
  let base ← mkAppM ``Lynth.Sat.FinVal.cellsCNF
    #[mkNatLit n, mkNatLit k]
  let mut fams : List Expr := []
  for fr in frags do
    fams := fams ++ [← mkFamBody fr gin n k]
  let comps := fams ++ [base]
  pure (← appendChain comps, comps)

/-- Split a held append chain into per-component held proofs,
mirroring `appendChain` over explicit component terms. -/
def splitHeld (m h : Expr) : List Expr → MetaM (List Expr)
  | [] => pure []
  | [_] => pure [h]
  | c :: cs => do
    let rest ← appendChain cs
    let pr ← mkAppM ``Lynth.Sat.Gates.checkSat_appendHeld #[c, rest, m, h]
    let hl ← mkAppM ``And.left #[pr]
    let hr ← mkAppM ``And.right #[pr]
    pure (hl :: (← splitHeld m hr cs))

/-- Closed encoder `input → CNF`: every family plus one-hot rows,
right-nested (`fam_0 ++ (... ++ cells)`) matching `liftMem`. -/
def mkEncode (frags : List Frag) (n k : Nat) (inTy : Expr) :
    MetaM Expr := do
  withLocalDeclD `input inTy fun gin => do
    let (body, _) ← mkEncodeBody gin frags n k
    mkLambdaFVars #[gin] body

/-- Assignment type term. -/
def assignTy : MetaM Expr := do
  let bool := mkConst ``Bool []
  let opt := mkApp (mkConst ``Option [Level.zero]) bool
  pure (mkApp (mkConst ``List [Level.zero]) opt)

/-- Closed decoder `Assignment → Fin n → Fin k`. -/
def mkDecode (n k : Nat) (hk : Expr) : MetaM Expr := do
  withLocalDeclD `m (← assignTy) fun m =>
  withLocalDeclD `v (finTyLit n) fun v => do
    let d ← mkAppM ``Lynth.Sat.FinVal.decodeVal
      #[mkNatLit n, mkNatLit k, hk, m, v]
    mkLambdaFVars #[m, v] d

/-- Total-solver fuel constants (mirroring the eager engine). -/
def compileFuel : Nat := 2000000
def compileRestart : Nat := 100

/-- Combine per-conjunct proofs into whole-conjunction, mirroring
right-nested `And` from `splitConj`. -/
def combineConj : List Expr → MetaM Expr
  | [] => throwError "combineConj: empty"
  | [p] => pure p
  | p :: ps => do
    let rest ← combineConj ps
    mkAppM ``And.intro #[p, rest]

/-- Split a held conjunction hypothesis into per-conjunct proofs,
mirroring right-nested `And` chains. Index `0` is the first conjunct. -/
def conjProj (hPf : Expr) (idx total : Nat) : MetaM Expr := do
  if total <= 1 then pure hPf
  else if idx == 0 then mkAppM ``And.left #[hPf]
  else
    let rest ← conjProj hPf (idx - 1) (total - 1)
    mkAppM ``And.right #[rest]

/-- Combine per-component held proofs into whole-held, mirroring
`appendChain` over explicit component terms. -/
def combineHeld (m : Expr) : List Expr → List Expr → MetaM Expr
  | [], _ => throwError "combineHeld: empty"
  | [p], [_] => pure p
  | p :: ps, c :: cs => do
    let rest ← appendChain cs
    let restH ← combineHeld m ps cs
    mkAppM ``Lynth.Sat.Gates.appendHeld #[c, rest, m, p, restH]
  | _, _ => throwError "combineHeld: length mismatch"

/-- Lift clause membership into a right-nested append chain
`f_0 ++ (... ++ cells)`: family `j < m` descends `j` rights then
left; cells (`j = m`) descends `m` rights. -/
def liftMem (hc : Expr) (j m : Nat) : MetaM Expr := do
  match j with
  | 0 => if m == 0 then pure hc else mkAppM ``Or.inl #[hc]
  | j + 1 =>
    let rest ← liftMem hc j (m - 1)
    mkAppM ``Or.inr #[rest]
def runSolver {I O : Type} (encode : I → CNF)
    (decode : Assignment → O)
    (fuel restartBase : Nat) (input : I) :
    Option O := 
  match solveTotal (encode input) fuel restartBase (∅ : Std.HashSet Nat) with
  | .sat m => some (decode m)
  | .unsat => none

/-- Runner soundness from a decode lemma. -/
theorem runSolver_sound {I O : Type} (encode : I → CNF)
    (decode : Assignment → O) (P : I → O → Prop)
    (fuel restartBase : Nat)
    (hsound : ∀ input m,
      checkSat (encode input) m = true → P input (decode m))
    (input : I) (out : O)
    (h : runSolver encode decode fuel restartBase input
      = some out) :
    P input out := by
  unfold runSolver at h
  match hR : solveTotal (encode input) fuel restartBase (∅ : Std.HashSet Nat) with
  | .sat m =>
    simp only [hR] at h
    obtain rfl := Option.some.inj h
    exact hsound input m (solveTotal_sound _ _ _ _ m hR)
  | .unsat =>
    simp only [hR] at h
    nomatch h

/-- Runner completeness from an encode lemma. -/
theorem runSolver_complete {I O : Type} (encode : I → CNF)
    (decode : Assignment → O) (P : I → O → Prop)
    (fuel restartBase : Nat)
    (hcomp : ∀ input f, P input f → ∃ m, checkSat (encode input) m = true)
    (input : I) (hex : ∃ f, P input f) :
    ∃ out, runSolver encode decode fuel restartBase input
      = some out := by
  obtain ⟨f, hf⟩ := hex
  obtain ⟨m, hm⟩ := hcomp input f hf
  match hR : solveTotal (encode input) fuel restartBase (∅ : Std.HashSet Nat) with
  | .sat m' =>
    exact ⟨decode m', by unfold runSolver; rw [hR]⟩
  | .unsat =>
    have hfalse := solveTotal_complete _ _ _ _ m hR
    rw [hm] at hfalse
    exact Bool.noConfusion hfalse

/-- Runner none-iff from both directions. -/
theorem runSolver_none {I O : Type} (encode : I → CNF)
    (decode : Assignment → O) (P : I → O → Prop)
    (fuel restartBase : Nat)
    (hsound : ∀ input m,
      checkSat (encode input) m = true → P input (decode m))
    (hcomp : ∀ input f, P input f → ∃ m, checkSat (encode input) m = true)
    (input : I) :
    runSolver encode decode fuel restartBase input = none ↔
      ¬∃ out, P input out := by
  constructor
  · intro hnone hex
    obtain ⟨out, ho⟩ := hex
    match hR : solveTotal (encode input) fuel restartBase (∅ : Std.HashSet Nat) with
    | .sat m =>
      unfold runSolver at hnone
      rw [hR] at hnone
      simp at hnone
    | .unsat =>
      obtain ⟨m, hm⟩ := hcomp input out ho
      have hfalse := solveTotal_complete _ _ _ _ m hR
      rw [hm] at hfalse
      exact Bool.noConfusion hfalse
  · intro hne
    match hR : solveTotal (encode input) fuel restartBase (∅ : Std.HashSet Nat) with
    | .sat m =>
      have hp := hsound input m (solveTotal_sound _ _ _ _ m hR)
      exact absurd ⟨decode m, hp⟩ hne
    | .unsat =>
      unfold runSolver
      rw [hR]

/-- Classify one conjunction-split validity body into fragments.
All shapes, one table-driven pass; anything unrecognized yields
`none` (conservative: later fragments extend the table). -/
def matchFrag (P : Expr) : MetaM (Option (List Frag)) := do
  let PR ← whnf P
  lambdaTelescope PR fun lams bodyLam => do
    if lams.size != 2 then pure none
    else
      let g := lams[0]!
      let c := lams[1]!
      -- single-level `Fin n → Fin k` outputs in v1
      let outTyR ← whnf (← inferType c)
      match outTyR with
      | .forallE _ dom cod _ =>
        if cod.hasLooseBVars then pure none
        else
          match ← finBound dom, ← finBound cod with
          | some n, some k =>
            let mut frags : List Frag := []
            for cj in splitConj bodyLam do
              -- injectivity head
              match ← matchInj cj c with
              | some _ =>
                frags := ⟨.inj, n, k,
                  ← mkLambdaFVars #[g] (mkConst ``Bool.true [])⟩ :: frags
              | none =>
                -- `∀∀`-guarded shapes
                let ij ← forallBoundedTelescope cj (some 2) fun fvs rest => do
                  if fvs.size != 2 then pure (none : Option (FragKind × Expr))
                  else
                    match ← finBound (← inferType fvs[0]!),
                        ← finBound (← inferType fvs[1]!) with
                    | some n1, some n2 =>
                      if n1 != n || n2 != n then pure none
                      else
                        match ← matchGuardNeBody rest with
                        | none =>
                          pure none
                        | some (guardApp, lhs, rhs, isNe) =>
                          -- sides must be output applications
                          match lhs.getAppFn, rhs.getAppFn with
                          | .fvar fc, .fvar fc2 =>
                            if fc != c.fvarId! || fc2 != c.fvarId! then
                              pure none
                            else
                              let gl ← mkLambdaFVars
                                #[g, fvs[0]!, fvs[1]!] guardApp
                              pure (some
                                ((if isNe then FragKind.ne else FragKind.eq),
                                  gl))
                          | _, _ =>
                            pure none
                    | _, _ => pure none
                match ij with
                | some (kind, gl) =>
                  frags := ⟨kind, n, k, gl⟩ :: frags
                | none => return none
            pure (some frags.reverse)
          | _, _ => pure none
      | _ => pure none

end Lynth.Sat.Compile
