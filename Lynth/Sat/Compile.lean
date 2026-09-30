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

/-- Fragment kinds: v1 covers single-level `Fin` outputs;
v1b adds two-dimensional boards (`Fin n → Fin n → Fin k`,
linearized to `Fin (n*n)`). Multi-index outputs and arithmetic
arrive as later fragments without touching this code. -/
inductive FragKind
  | ne
  | eq
  | inj
  | req
  | row
  | col
  | box
  | given
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

/-- Scoped injectivity family: pairwise difference over an
explicit cell list (rows, columns, boxes share this one construction). -/
def injListCNF (N k : Nat) (cells : List (Fin N)) : CNF :=
  cells.flatMap fun u =>
    cells.flatMap fun v =>
      condDiffPair k u.val v.val (decide (u ≠ v))

/-- Scoped injectivity soundness. -/
theorem injList_sound (N k : Nat) (hk : 0 < k) (cells : List (Fin N))
    (m : Assignment)
    (hrows : ∀ v ∈ cells,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (injListCNF N k cells) m = true) :
    ∀ a ∈ cells, ∀ b ∈ cells,
      decodeVal N k hk m a = decodeVal N k hk m b → a = b := by
  intro a ha b hb hab
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
      refine ⟨a, ha, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨b, hb, ?_⟩
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
    have hdn := diff_sound_decode N k hk m a b
      (hrows a ha) (hrows b hb) hper
    exact absurd hab hdn

/-- Scoped injectivity completeness. -/
theorem injList_complete (N k : Nat) (hk : 0 < k) (cells : List (Fin N))
    (f : Fin N → Fin k)
    (hinj : ∀ a ∈ cells, ∀ b ∈ cells, f a = f b → a = b) :
    checkSat (injListCNF N k cells) (modelOf N k f) = true := by
  apply checkSat_flatMap
  intro u hum
  apply checkSat_flatMap
  intro v hvm
  by_cases heq : u = v
  · have hgf : decide (u ≠ v) = false := by simp [heq]
    have h0 : condDiffPair k u.val v.val (decide (u ≠ v)) = [] := by
      simp [condDiffPair, condClauses, hgf]
    change checkSat (condDiffPair k u.val v.val (decide (u ≠ v)))
      (modelOf N k f) = true
    rw [h0]
    rfl
  · have hne : u ≠ v := heq
    have hg : decide (u ≠ v) = true := decide_eq_true hne
    have h2 : checkSat (diffCNF k [(u.val, v.val)]) (modelOf N k f)
        = true :=
      diffCNF_complete N k hk f u v (fun h => hne (hinj u hum v hvm h))
    have h3 : checkSat (condDiffPair k u.val v.val (decide (u ≠ v)))
        (modelOf N k f) = true :=
      condClauses_of_true _ _ _ hg h2
    simpa [condDiffPair] using h3

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

/-- 2D index linearization: `(r, c)` over `Fin 9` to `Fin 81`.
Sizes are puzzle parameters (like `n = 8` for coloring); the shape
is generic. All bounds discharge by `omega`/`decide` on literals. -/
def lin2D (r c : Fin 9) : Fin 81 :=
  ⟨r.val * 9 + c.val, by omega⟩

/-- Inverse: split a linear cell back into row/col. -/
def unlin2D (i : Fin 81) : Fin 9 × Fin 9 :=
  (⟨i.val / 9, by omega⟩, ⟨i.val % 9, by omega⟩)

/-- Linearization is injective on pairs. -/
theorem lin2D_inj (r₁ c₁ r₂ c₂ : Fin 9)
    (h : lin2D r₁ c₁ = lin2D r₂ c₂) : r₁ = r₂ ∧ c₁ = c₂ := by
  have h1 := r₁.isLt
  have h2 := c₁.isLt
  have h3 := r₂.isLt
  have h4 := c₂.isLt
  have hv : r₁.val * 9 + c₁.val = r₂.val * 9 + c₂.val := by
    have h0 := congrArg Fin.val h
    simpa [lin2D] using h0
  have hr : r₁.val = r₂.val := by omega
  have hc : c₁.val = c₂.val := by omega
  exact ⟨Fin.ext hr, Fin.ext hc⟩

/-- Roundtrip: unlinearizing is left-inverse. -/
theorem unlin_lin (r c : Fin 9) :
    unlin2D (lin2D r c) = (r, c) := by
  have h1 := r.isLt
  have h2 := c.isLt
  simp only [unlin2D, lin2D]
  have hr : (r.val * 9 + c.val) / 9 = r.val := by omega
  have hc : (r.val * 9 + c.val) % 9 = c.val := by omega
  simp [hr, hc, Fin.ext_iff]

/-- Linear roundtrip the other way: linearizing the split. -/
theorem lin_unlin (i : Fin 81) :
    lin2D (unlin2D i).1 (unlin2D i).2 = i := by
  have h0 := i.isLt
  simp only [unlin2D, lin2D]
  have hdiv : i.val / 9 < 9 := by omega
  have hmod : i.val % 9 < 9 := by omega
  -- `(i/9)*9 + i%9 = i` then `Fin.ext`
  have hdm : (i.val / 9) * 9 + i.val % 9 = i.val := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod _ _
  apply Fin.ext
  show (i.val / 9) * 9 + i.val % 9 = i.val
  exact hdm

/-- Row guard over linear cells: same row plus distinctness. -/
def rowGuard81 (i j : Fin 81) : Bool :=
  decide ((unlin2D i).1 = (unlin2D j).1 ∧ i ≠ j)

/-- Column guard over linear cells. -/
def colGuard81 (i j : Fin 81) : Bool :=
  decide ((unlin2D i).2 = (unlin2D j).2 ∧ i ≠ j)

/-- Row adequacy (sound): linear guarded difference gives nested
row injectivity. -/
theorem rowAdequate_sound (f : Fin 81 → Fin 9)
    (hne : ∀ i j : Fin 81, rowGuard81 i j = true → f i ≠ f j) :
    ∀ r c₁ c₂ : Fin 9, f (lin2D r c₁) = f (lin2D r c₂) → c₁ = c₂ := by
  intro r c₁ c₂ hve
  by_contra hne2
  have hpne : lin2D r c₁ ≠ lin2D r c₂ := by
    intro hcon
    have hpair := (lin2D_inj r c₁ r c₂ hcon).2
    exact hne2 hpair
  have hg : rowGuard81 (lin2D r c₁) (lin2D r c₂) = true := by
    unfold rowGuard81
    apply decide_eq_true
    refine ⟨?_, hpne⟩
    have h1 : (unlin2D (lin2D r c₁)).1 = r := by
      rw [unlin_lin]
    have h2 : (unlin2D (lin2D r c₂)).1 = r := by
      rw [unlin_lin]
    rw [h1, h2]
  exact absurd hve (hne _ _ hg)

/-- Column adequacy (sound). -/
theorem colAdequate_sound (f : Fin 81 → Fin 9)
    (hne : ∀ i j : Fin 81, colGuard81 i j = true → f i ≠ f j) :
    ∀ c r₁ r₂ : Fin 9, f (lin2D r₁ c) = f (lin2D r₂ c) → r₁ = r₂ := by
  intro c r₁ r₂ hve
  by_contra hne2
  have hpne : lin2D r₁ c ≠ lin2D r₂ c := by
    intro hcon
    have hpair := (lin2D_inj r₁ c r₂ c hcon).1
    exact hne2 hpair
  have hg : colGuard81 (lin2D r₁ c) (lin2D r₂ c) = true := by
    unfold colGuard81
    apply decide_eq_true
    refine ⟨?_, hpne⟩
    have h1 : (unlin2D (lin2D r₁ c)).2 = c := by
      rw [unlin_lin]
    have h2 : (unlin2D (lin2D r₂ c)).2 = c := by
      rw [unlin_lin]
    rw [h1, h2]
  exact absurd hve (hne _ _ hg)

/-- Column adequacy (complete). -/
theorem colAdequate_complete (f : Fin 81 → Fin 9)
    (hvalid : ∀ c r₁ r₂ : Fin 9,
      f (lin2D r₁ c) = f (lin2D r₂ c) → r₁ = r₂) :
    ∀ i j : Fin 81, colGuard81 i j = true → f i ≠ f j := by
  intro i j hg
  have hsame : (unlin2D i).2 = (unlin2D j).2 :=
    (of_decide_eq_true hg).1
  have hne : i ≠ j := (of_decide_eq_true hg).2
  intro hcon
  have hi : i = lin2D (unlin2D i).1 (unlin2D i).2 := (lin_unlin i).symm
  have hj : j = lin2D (unlin2D j).1 (unlin2D j).2 := (lin_unlin j).symm
  have hve : f (lin2D (unlin2D i).1 (unlin2D i).2) =
      f (lin2D (unlin2D j).1 (unlin2D j).2) := by
    rw [← hi, ← hj]
    exact hcon
  rw [hsame] at hve
  have hcc := hvalid _ _ _ hve
  have hpp : ((unlin2D i).1, (unlin2D i).2) =
      ((unlin2D j).1, (unlin2D j).2) :=
    Prod.ext hcc hsame
  have hij : i = j := by
    have hll := congrArg (fun p : Fin 9 × Fin 9 => lin2D p.1 p.2) hpp
    rwa [lin_unlin, lin_unlin] at hll
  exact hne hij

/-- Row adequacy (complete). -/
theorem rowAdequate_complete (f : Fin 81 → Fin 9)
    (hvalid : ∀ r c₁ c₂ : Fin 9,
      f (lin2D r c₁) = f (lin2D r c₂) → c₁ = c₂) :
    ∀ i j : Fin 81, rowGuard81 i j = true → f i ≠ f j := by
  intro i j hg
  have hsame : (unlin2D i).1 = (unlin2D j).1 :=
    (of_decide_eq_true hg).1
  have hne : i ≠ j := (of_decide_eq_true hg).2
  intro hcon
  have hi : i = lin2D (unlin2D i).1 (unlin2D i).2 := (lin_unlin i).symm
  have hj : j = lin2D (unlin2D j).1 (unlin2D j).2 := (lin_unlin j).symm
  have hve : f (lin2D (unlin2D i).1 (unlin2D i).2) =
      f (lin2D (unlin2D j).1 (unlin2D j).2) := by
    rw [← hi, ← hj]
    exact hcon
  rw [hsame] at hve
  have hcc := hvalid _ _ _ hve
  have hpp : ((unlin2D i).1, (unlin2D i).2) =
      ((unlin2D j).1, (unlin2D j).2) :=
    Prod.ext hsame hcc
  have hij : i = j := by
    have hll := congrArg (fun p : Fin 9 × Fin 9 => lin2D p.1 p.2) hpp
    rwa [lin_unlin, lin_unlin] at hll
  exact hne hij

/-- Pure box guard lifted to linear cells. `boxB` is the decidable
user condition (e.g. same `box_idx`); the linear guard adds
distinctness. Frag wrappers ignore the input to keep the uniform
`input → Fin 81 → Fin 81 → Bool` contract. -/
def boxGuardLin (boxB : Fin 9 → Fin 9 → Fin 9 → Fin 9 → Bool)
    (i j : Fin 81) : Bool :=
  boxB (unlin2D i).1 (unlin2D i).2 (unlin2D j).1 (unlin2D j).2 &&
    decide (i ≠ j)

/-- Box adequacy (sound): linear guarded difference gives the nested
paired conclusion. -/
theorem boxAdequate_sound (boxB : Fin 9 → Fin 9 → Fin 9 → Fin 9 → Bool)
    (f : Fin 81 → Fin 9)
    (hne : ∀ i j : Fin 81, boxGuardLin boxB i j = true → f i ≠ f j) :
    ∀ r₁ c₁ r₂ c₂ : Fin 9, boxB r₁ c₁ r₂ c₂ = true →
      f (lin2D r₁ c₁) = f (lin2D r₂ c₂) → r₁ = r₂ ∧ c₁ = c₂ := by
  intro r₁ c₁ r₂ c₂ hb hve
  by_contra hcon
  have hne_lin : lin2D r₁ c₁ ≠ lin2D r₂ c₂ := by
    intro heq
    exact hcon (lin2D_inj r₁ c₁ r₂ c₂ heq)
  have hg : boxGuardLin boxB (lin2D r₁ c₁) (lin2D r₂ c₂) = true := by
    unfold boxGuardLin
    have h1 : (unlin2D (lin2D r₁ c₁)).1 = r₁ := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r₁ c₁)).2 = c₁ := by rw [unlin_lin]
    have h3 : (unlin2D (lin2D r₂ c₂)).1 = r₂ := by rw [unlin_lin]
    have h4 : (unlin2D (lin2D r₂ c₂)).2 = c₂ := by rw [unlin_lin]
    rw [h1, h2, h3, h4]
    have hd : decide (lin2D r₁ c₁ ≠ lin2D r₂ c₂) = true :=
      decide_eq_true hne_lin
    simp [hb, hd]
  exact absurd hve (hne _ _ hg)

/-- Box adequacy (complete). -/
theorem boxAdequate_complete (boxB : Fin 9 → Fin 9 → Fin 9 → Fin 9 → Bool)
    (f : Fin 81 → Fin 9)
    (hvalid : ∀ r₁ c₁ r₂ c₂ : Fin 9, boxB r₁ c₁ r₂ c₂ = true →
      f (lin2D r₁ c₁) = f (lin2D r₂ c₂) → r₁ = r₂ ∧ c₁ = c₂) :
    ∀ i j : Fin 81, boxGuardLin boxB i j = true → f i ≠ f j := by
  intro i j hg
  have hpair : boxB (unlin2D i).1 (unlin2D i).2
      (unlin2D j).1 (unlin2D j).2 = true ∧ decide (i ≠ j) = true :=
    (Bool.and_eq_true_iff.mp hg)
  have hb := hpair.1
  have hne : i ≠ j := of_decide_eq_true hpair.2
  intro hcon
  have hi : i = lin2D (unlin2D i).1 (unlin2D i).2 := (lin_unlin i).symm
  have hj : j = lin2D (unlin2D j).1 (unlin2D j).2 := (lin_unlin j).symm
  have hve : f (lin2D (unlin2D i).1 (unlin2D i).2) =
      f (lin2D (unlin2D j).1 (unlin2D j).2) := by
    rw [← hi, ← hj]
    exact hcon
  have hconc := hvalid _ _ _ _ hb hve
  have hpp : ((unlin2D i).1, (unlin2D i).2) =
      ((unlin2D j).1, (unlin2D j).2) :=
    Prod.ext hconc.1 hconc.2
  have hij : i = j := by
    have hll := congrArg (fun p : Fin 9 × Fin 9 => lin2D p.1 p.2) hpp
    rwa [lin_unlin, lin_unlin] at hll
  exact hne hij

/-- Input-dependent given guard lifted through unlinearization. -/
def givenGuardLin (I : Type)
    (givB : I → Fin 9 → Fin 9 → Fin 9 → Bool)
    (input : I) (i : Fin 81) (v : Fin 9) : Bool :=
  givB input (unlin2D i).1 (unlin2D i).2 v

/-- Given adequacy (sound): forced linear values give nested givens. -/
theorem givenAdequate_sound (I : Type)
    (givB : I → Fin 9 → Fin 9 → Fin 9 → Bool)
    (input : I) (f : Fin 81 → Fin 9)
    (hforced : ∀ i : Fin 81, ∀ vv : Fin 9,
      givenGuardLin _ givB input i vv = true → f i = vv) :
    ∀ r c v : Fin 9, givB input r c v = true → f (lin2D r c) = v := by
  intro r c v hb
  have hg : givenGuardLin _ givB input (lin2D r c) v = true := by
    unfold givenGuardLin
    have h1 : (unlin2D (lin2D r c)).1 = r := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r c)).2 = c := by rw [unlin_lin]
    rw [h1, h2]
    exact hb
  exact hforced _ _ hg

/-- Given adequacy (complete). -/
theorem givenAdequate_complete (I : Type)
    (givB : I → Fin 9 → Fin 9 → Fin 9 → Bool)
    (input : I) (f : Fin 81 → Fin 9)
    (hvalid : ∀ r c v : Fin 9, givB input r c v = true →
      f (lin2D r c) = v) :
    ∀ i : Fin 81, ∀ v : Fin 9,
      givenGuardLin _ givB input i v = true → f i = v := by
  intro i v hb
  have hi : i = lin2D (unlin2D i).1 (unlin2D i).2 := (lin_unlin i).symm
  have hlin : givB input (unlin2D i).1 (unlin2D i).2 v = true := hb
  have h := hvalid _ _ _ hlin
  rw [hi]
  exact h

/-- Forced-value family over all index/value pairs. -/
def givenFamCNF (I : Type) (n k : Nat)
    (guard : I → Fin n → Fin k → Bool) (input : I) : CNF :=
  (List.finRange n).flatMap fun i =>
    (List.finRange k).flatMap fun v =>
      condUnitPos k i.val v.val (guard input i v)

/-- Fragment soundness (forced values). -/
theorem givenFam_sound (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin k → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin n,
      checkSat (oneHotRowCNF (rowLits k v.val)) m = true)
    (hfam : checkSat (givenFamCNF I n k guard input) m = true) :
    ∀ i : Fin n, ∀ c : Fin k, guard input i c = true →
      decodeVal n k hk m i = c := by
  intro i c hg
  have hper : ∀ c' : Fin k, checkSat
      (condUnitPos k i.val c'.val (guard input i c')) m = true := by
    intro c'
    by_cases hg' : guard input i c' = true
    · have hunit : condUnitPos k i.val c'.val (guard input i c')
          = [[Int.ofNat (idxVar k i.val c'.val)]] := by
        simp [condUnitPos, condClauses, hg']
      apply checkSat_of_all_single
      intro cl hc
      rw [hunit] at hc
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
      subst hc
      apply checkSat_mem m _ _ _ hfam
      apply List.mem_flatMap.mpr
      refine ⟨i, List.mem_finRange i, ?_⟩
      apply List.mem_flatMap.mpr
      refine ⟨c', List.mem_finRange c', ?_⟩
      change [Int.ofNat (idxVar k i.val c'.val)] ∈
        condUnitPos k i.val c'.val (guard input i c')
      rw [hunit]
      exact List.mem_cons_self
    · have hempty : condUnitPos k i.val c'.val (guard input i c') = [] := by
        have hgf : guard input i c' = false :=
          Bool.eq_false_of_ne_true hg'
        simp [condUnitPos, condClauses, hgf]
      rw [hempty]
      rfl
  exact unitPos_sound n k (guard input) hk m i (hrows i) hper c hg

/-- Fragment completeness (forced values). -/
theorem givenFam_complete (I : Type) (n k : Nat) (hk : 0 < k)
    (guard : I → Fin n → Fin k → Bool) (input : I)
    (f : Fin n → Fin k)
    (hvalid : ∀ i : Fin n, ∀ c : Fin k, guard input i c = true → f i = c) :
    checkSat (givenFamCNF I n k guard input) (modelOf n k f) = true := by
  apply checkSat_flatMap
  intro i him
  apply checkSat_flatMap
  intro v hvm
  exact unitPos_complete n k (guard input) hk f i
    (fun c hc => hvalid i c hc) v

/-- Row nested soundness (combined): held `ne` family with a
`rowGuard81` wrapper decodes to nested row injectivity. -/
theorem rowNested_sound (I : Type)
    (guard : I → Fin 81 → Fin 81 → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin 81,
      checkSat (oneHotRowCNF (rowLits 9 v.val)) m = true)
    (hfam : checkSat (neFamCNF I 81 9 guard input) m = true)
    (hguard : ∀ i j : Fin 81, guard input i j = rowGuard81 i j) :
    ∀ r c₁ c₂ : Fin 9,
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r c₁) =
        decodeVal 81 9 (by decide : 0 < 9) m (lin2D r c₂) → c₁ = c₂ := by
  have hne : ∀ i j : Fin 81, rowGuard81 i j = true →
      decodeVal 81 9 (by decide : 0 < 9) m i ≠
        decodeVal 81 9 (by decide : 0 < 9) m j := by
    intro i j hg
    have hg' : guard input i j = true := by rw [hguard]; exact hg
    exact neFam_sound I 81 9 (by decide : 0 < 9) guard input m hrows hfam i j hg'
  exact rowAdequate_sound _ hne

/-- Row nested completeness (combined): nested row validity yields a
held `ne` family for the unlinearized model. -/
theorem rowNested_complete (I : Type)
    (guard : I → Fin 81 → Fin 81 → Bool) (input : I)
    (f : Fin 9 → Fin 9 → Fin 9)
    (hvalid : ∀ r c₁ c₂ : Fin 9, f r c₁ = f r c₂ → c₁ = c₂)
    (hguard : ∀ i j : Fin 81, guard input i j = rowGuard81 i j) :
    checkSat (neFamCNF I 81 9 guard input)
      (modelOf 81 9 (fun i => f (unlin2D i).1 (unlin2D i).2)) = true := by
  have hvalidLin : ∀ r c₁ c₂ : Fin 9,
      (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r c₁) =
        (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r c₂) → c₁ = c₂ := by
    intro r c₁ c₂ hve
    have h1 : (unlin2D (lin2D r c₁)).1 = r := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r c₁)).2 = c₁ := by rw [unlin_lin]
    have h3 : (unlin2D (lin2D r c₂)).1 = r := by rw [unlin_lin]
    have h4 : (unlin2D (lin2D r c₂)).2 = c₂ := by rw [unlin_lin]
    simp only at hve
    rw [h1, h2, h3, h4] at hve
    exact hvalid r c₁ c₂ hve
  have hne : ∀ i j : Fin 81, rowGuard81 i j = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) i ≠
        (fun i => f (unlin2D i).1 (unlin2D i).2) j :=
    rowAdequate_complete _ hvalidLin
  apply neFam_complete I 81 9 (by decide : 0 < 9) guard input _ _ 
  intro i j hg
  have hg' : rowGuard81 i j = true := by rw [← hguard]; exact hg
  exact hne i j hg'

/-- Column nested soundness (combined). -/
theorem colNested_sound (I : Type)
    (guard : I → Fin 81 → Fin 81 → Bool) (input : I) (m : Assignment)
    (hrows : ∀ v : Fin 81,
      checkSat (oneHotRowCNF (rowLits 9 v.val)) m = true)
    (hfam : checkSat (neFamCNF I 81 9 guard input) m = true)
    (hguard : ∀ i j : Fin 81, guard input i j = colGuard81 i j) :
    ∀ c r₁ r₂ : Fin 9,
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₁ c) =
        decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₂ c) → r₁ = r₂ := by
  have hne : ∀ i j : Fin 81, colGuard81 i j = true →
      decodeVal 81 9 (by decide : 0 < 9) m i ≠
        decodeVal 81 9 (by decide : 0 < 9) m j := by
    intro i j hg
    have hg' : guard input i j = true := by rw [hguard]; exact hg
    exact neFam_sound I 81 9 (by decide : 0 < 9) guard input m hrows hfam i j hg'
  exact colAdequate_sound _ hne

/-- Column nested completeness (combined). -/
theorem colNested_complete (I : Type)
    (guard : I → Fin 81 → Fin 81 → Bool) (input : I)
    (f : Fin 9 → Fin 9 → Fin 9)
    (hvalid : ∀ c r₁ r₂ : Fin 9, f r₁ c = f r₂ c → r₁ = r₂)
    (hguard : ∀ i j : Fin 81, guard input i j = colGuard81 i j) :
    checkSat (neFamCNF I 81 9 guard input)
      (modelOf 81 9 (fun i => f (unlin2D i).1 (unlin2D i).2)) = true := by
  have hvalidLin : ∀ c r₁ r₂ : Fin 9,
      (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r₁ c) =
        (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r₂ c) → r₁ = r₂ := by
    intro c r₁ r₂ hve
    have h1 : (unlin2D (lin2D r₁ c)).1 = r₁ := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r₁ c)).2 = c := by rw [unlin_lin]
    have h3 : (unlin2D (lin2D r₂ c)).1 = r₂ := by rw [unlin_lin]
    have h4 : (unlin2D (lin2D r₂ c)).2 = c := by rw [unlin_lin]
    simp only at hve
    rw [h1, h2, h3, h4] at hve
    exact hvalid c r₁ r₂ hve
  have hne : ∀ i j : Fin 81, colGuard81 i j = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) i ≠
        (fun i => f (unlin2D i).1 (unlin2D i).2) j :=
    colAdequate_complete _ hvalidLin
  apply neFam_complete I 81 9 (by decide : 0 < 9) guard input _ _
  intro i j hg
  have hg' : colGuard81 i j = true := by rw [← hguard]; exact hg
  exact hne i j hg'

/-- Box nested soundness (combined, `Prop` antecedent matching
goals): held `ne` family with a `boxGuardLin` wrapper decodes to
paired indices whenever the user `lhs = rhs` holds. `beq_iff_eq`
bridges `==`/`=` inside. -/
theorem boxNested_sound (boxLHS boxRHS : Fin 9 → Fin 9 → Fin 9 → Fin 9 → Fin 9)
    (I : Type) (guard : I → Fin 81 → Fin 81 → Bool) (input : I)
    (m : Assignment)
    (hrows : ∀ v : Fin 81,
      checkSat (oneHotRowCNF (rowLits 9 v.val)) m = true)
    (hfam : checkSat (neFamCNF I 81 9 guard input) m = true)
    (hguard : ∀ i j : Fin 81, guard input i j =
      boxGuardLin (fun a b c d => (boxLHS a b c d == boxRHS a b c d)) i j) :
    ∀ r₁ c₁ r₂ c₂ : Fin 9,
      boxLHS r₁ c₁ r₂ c₂ = boxRHS r₁ c₁ r₂ c₂ →
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₁ c₁) =
        decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₂ c₂) →
      r₁ = r₂ ∧ c₁ = c₂ := by
  have hne : ∀ i j : Fin 81,
      boxGuardLin (fun a b c d => (boxLHS a b c d == boxRHS a b c d)) i j = true →
      decodeVal 81 9 (by decide : 0 < 9) m i ≠
        decodeVal 81 9 (by decide : 0 < 9) m j := by
    intro i j hg
    have hg' : guard input i j = true := by rw [hguard]; exact hg
    exact neFam_sound I 81 9 (by decide : 0 < 9) guard input m hrows hfam i j hg'
  have hbox : ∀ r₁ c₁ r₂ c₂ : Fin 9,
      (boxLHS r₁ c₁ r₂ c₂ == boxRHS r₁ c₁ r₂ c₂) = true →
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₁ c₁) =
        decodeVal 81 9 (by decide : 0 < 9) m (lin2D r₂ c₂) →
      r₁ = r₂ ∧ c₁ = c₂ :=
    boxAdequate_sound _ _ hne
  intro r₁ c₁ r₂ c₂ hP hve
  have hb : (boxLHS r₁ c₁ r₂ c₂ == boxRHS r₁ c₁ r₂ c₂) = true :=
    (beq_iff_eq.mpr hP)
  exact hbox r₁ c₁ r₂ c₂ hb hve

/-- Box nested completeness (combined, `Prop` antecedent matching
goals): nested box validity with `lhs = rhs` yields a held family
for the unlinearized model. `beq_iff_eq` bridges `==`/`=` inside. -/
theorem boxNested_complete (boxLHS boxRHS : Fin 9 → Fin 9 → Fin 9 → Fin 9 → Fin 9)
    (I : Type) (guard : I → Fin 81 → Fin 81 → Bool) (input : I)
    (f : Fin 9 → Fin 9 → Fin 9)
    (hvalid : ∀ r₁ c₁ r₂ c₂ : Fin 9,
      boxLHS r₁ c₁ r₂ c₂ = boxRHS r₁ c₁ r₂ c₂ →
      f r₁ c₁ = f r₂ c₂ → r₁ = r₂ ∧ c₁ = c₂)
    (hguard : ∀ i j : Fin 81, guard input i j =
      boxGuardLin (fun a b c d => (boxLHS a b c d == boxRHS a b c d)) i j) :
    checkSat (neFamCNF I 81 9 guard input)
      (modelOf 81 9 (fun i => f (unlin2D i).1 (unlin2D i).2)) = true := by
  have hvalidBool : ∀ r₁ c₁ r₂ c₂ : Fin 9,
      (boxLHS r₁ c₁ r₂ c₂ == boxRHS r₁ c₁ r₂ c₂) = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r₁ c₁) =
        (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r₂ c₂) →
      r₁ = r₂ ∧ c₁ = c₂ := by
    intro r₁ c₁ r₂ c₂ hb hve
    have hP : boxLHS r₁ c₁ r₂ c₂ = boxRHS r₁ c₁ r₂ c₂ :=
      (beq_iff_eq.mp hb)
    have h1 : (unlin2D (lin2D r₁ c₁)).1 = r₁ := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r₁ c₁)).2 = c₁ := by rw [unlin_lin]
    have h3 : (unlin2D (lin2D r₂ c₂)).1 = r₂ := by rw [unlin_lin]
    have h4 : (unlin2D (lin2D r₂ c₂)).2 = c₂ := by rw [unlin_lin]
    simp only at hve
    rw [h1, h2, h3, h4] at hve
    exact hvalid r₁ c₁ r₂ c₂ hP hve
  have hne : ∀ i j : Fin 81,
      boxGuardLin (fun a b c d => (boxLHS a b c d == boxRHS a b c d)) i j = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) i ≠
        (fun i => f (unlin2D i).1 (unlin2D i).2) j :=
    boxAdequate_complete _ _ hvalidBool
  apply neFam_complete I 81 9 (by decide : 0 < 9) guard input _ _
  intro i j hg
  have hg' : boxGuardLin
      (fun a b c d => (boxLHS a b c d == boxRHS a b c d)) i j = true := by
    rw [← hguard]; exact hg
  exact hne i j hg'

/-- Given nested soundness (combined, `Prop` antecedent matching
goals with `input r c = some v`). -/
theorem givenNested_sound
    (guard : (Fin 9 → Fin 9 → Option (Fin 9)) → Fin 81 → Fin 9 → Bool)
    (input : Fin 9 → Fin 9 → Option (Fin 9)) (m : Assignment)
    (hrows : ∀ v : Fin 81,
      checkSat (oneHotRowCNF (rowLits 9 v.val)) m = true)
    (hfam : checkSat (givenFamCNF _ 81 9 guard input) m = true)
    (hguard : ∀ i : Fin 81, ∀ v : Fin 9, guard input i v =
      givenGuardLin _ (fun inp a b c => (inp a b == some c)) input i v) :
    ∀ r c v : Fin 9, input r c = some v →
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r c) = v := by
  have hforced : ∀ i : Fin 81, ∀ vv : Fin 9,
      givenGuardLin _ (fun inp a b c => (inp a b == some c)) input i vv = true →
      decodeVal 81 9 (by decide : 0 < 9) m i = vv := by
    intro i vv hg
    have hg' : guard input i vv = true := by rw [hguard]; exact hg
    exact givenFam_sound _ 81 9 (by decide : 0 < 9) guard input m hrows hfam i vv hg'
  have hbool : ∀ r c v : Fin 9, (input r c == some v) = true →
      decodeVal 81 9 (by decide : 0 < 9) m (lin2D r c) = v :=
    givenAdequate_sound _ _ input _ hforced
  intro r c v hP
  have hb : (input r c == some v) = true := (beq_iff_eq.mpr hP)
  exact hbool r c v hb

/-- Given nested completeness (combined, `Prop` antecedent matching
goals with `input r c = some v`). -/
theorem givenNested_complete
    (guard : (Fin 9 → Fin 9 → Option (Fin 9)) → Fin 81 → Fin 9 → Bool)
    (input : Fin 9 → Fin 9 → Option (Fin 9))
    (f : Fin 9 → Fin 9 → Fin 9)
    (hvalid : ∀ r c v : Fin 9, input r c = some v → f r c = v)
    (hguard : ∀ i : Fin 81, ∀ v : Fin 9, guard input i v =
      givenGuardLin _ (fun inp a b c => (inp a b == some c)) input i v) :
    checkSat (givenFamCNF _ 81 9 guard input)
      (modelOf 81 9 (fun i => f (unlin2D i).1 (unlin2D i).2)) = true := by
  -- NOTE: `givB` here is fixed to `==` on `input r c` vs `some v`
  -- (the only shape the matcher accepts); generality over arbitrary
  -- `givB` would need separate `lhs/rhs` params like the box case.
  have hvalidBool : ∀ r c v : Fin 9,
      (input r c == some v) = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r c) = v := by
    intro r c v hb
    have hP : input r c = some v := (beq_iff_eq.mp hb)
    have h1 : (unlin2D (lin2D r c)).1 = r := by rw [unlin_lin]
    have h2 : (unlin2D (lin2D r c)).2 = c := by rw [unlin_lin]
    have h := hvalid r c v hP
    have hlin : (fun i => f (unlin2D i).1 (unlin2D i).2) (lin2D r c) = v := by
      simp only
      rw [h1, h2]
      exact h
    exact hlin
  have hforcedLin : ∀ i : Fin 81, ∀ v : Fin 9,
      givenGuardLin _ (fun inp a b c => (inp a b == some c)) input i v = true →
      (fun i => f (unlin2D i).1 (unlin2D i).2) i = v :=
    givenAdequate_complete _ _ input _ hvalidBool
  apply givenFam_complete _ 81 9 (by decide : 0 < 9) guard input _ _
  intro i vv hg
  have hg' : givenGuardLin _
      (fun inp a b c => (inp a b == some c)) input i vv = true := by
    rw [← hguard]; exact hg
  exact hforcedLin i vv hg'

/-- `Fin`-dimension spine plus leaf bound: `Fin d₀ → … → Fin k`
gives `([d₀, …], k)`. Literals only (direct or `OfNat`-wrapped).
Fuel-bounded (types here are shallow). -/
def finDimsTyAux : Nat → Expr → MetaM (Option (List Nat × Nat))
  | 0, _ => pure none
  | fuel + 1, ty => do
    let tyR ← whnf ty
    match tyR.getAppFn with
    | .const ``Fin _ =>
      let args := tyR.getAppArgs
      if args.isEmpty then pure none
      else
        match ← finBound ty with
        | some k => pure (some ([], k))
        | none => pure none
    | _ =>
      match tyR with
      | .forallE _ dom cod _ =>
        if cod.hasLooseBVars then pure none
        else
          match ← finBound dom with
          | none => pure none
          | some d =>
            match ← finDimsTyAux fuel cod with
            | none => pure none
            | some (ds, k) => pure (some (d :: ds, k))
      | _ => pure none

def finDimsTy : Expr → MetaM (Option (List Nat × Nat)) :=
  finDimsTyAux 8

/-- Unlinearize projections: `(unlin2D i).1` / `.2` as terms. -/
def unlinProj (i : Expr) : MetaM (Expr × Expr) := do
  let fin9 := mkApp (mkConst ``Fin []) (mkNatLit 9)
  let u := mkApp (mkConst ``Lynth.Sat.Compile.unlin2D []) i
  pure (mkAppN (mkConst ``Prod.fst [Level.zero, Level.zero]) #[fin9, fin9, u],
    mkAppN (mkConst ``Prod.snd [Level.zero, Level.zero]) #[fin9, fin9, u])

/-- Closed row/col guard over `Fin 81` ignoring the input:
`fun _ i j => rowGuard81/colGuard81 i j`. Keeps the uniform
`input → Fin 81 → Fin 81 → Bool` contract; `fr.guard input i j`
is definitionally the linear guard. -/
def mkRCGuardLam (inTy : Expr) (isRow : Bool) : MetaM Expr := do
  let fin81 := mkApp (mkConst ``Fin []) (mkNatLit 81)
  withLocalDeclD `gin inTy fun gin =>
  withLocalDeclD `ii fin81 fun ii =>
  withLocalDeclD `jj fin81 fun jj => do
    let app ← if isRow then mkAppM ``Lynth.Sat.Compile.rowGuard81 #[ii, jj]
      else mkAppM ``Lynth.Sat.Compile.colGuard81 #[ii, jj]
    mkLambdaFVars #[gin, ii, jj] app

/-- Classify one 9×9-board conjunct with nested output applications.
Produces `row`/`col` frags over `Fin 81` (boxes/givens follow the
same template next). -/
def matchNestedConj (g c : Expr) (cj : Expr) : MetaM (Option Frag) := do
  -- rows / cols: three `Fin 9` binders, Eq-antecedent, index conclusion.
  -- `cj` is already whnf’d by the caller; telescope unfolds defs.
  let cjW ← whnf cj
  forallBoundedTelescope cjW (some 3) fun fvs rest => do
    if fvs.size != 3 then pure none
    else
      let bs ← fvs.mapM fun v => do finBound (← inferType v)
      match bs[0]!, bs[1]!, bs[2]! with
      | some 9, some 9, some 9 =>
        match rest with
        | .forallE _ dom cod _ =>
          if cod.hasLooseBVars then pure none
          else
            let domR ← whnf dom
            match domR.getAppFn with
            | .const ``Eq _ =>
              let dargs := domR.getAppArgs
              if dargs.size != 3 then pure none
              else
                let (a1, a2) := (dargs[1]!, dargs[2]!)
                match a1.getAppFn, a2.getAppFn with
                | .fvar fc1, .fvar fc2 =>
                  if fc1 != c.fvarId! || fc2 != c.fvarId! then pure none
                  else
                    let as1 := a1.getAppArgs
                    let as2 := a2.getAppArgs
                    if as1.size != 2 || as2.size != 2 then pure none
                    else
                      let codR ← whnf cod
                      match codR.getAppFn with
                      | .const ``Eq _ =>
                        let cargs := codR.getAppArgs
                        if cargs.size != 3 then pure none
                        else
                          let (e1, e2) := (cargs[1]!, cargs[2]!)
                          let inTy ← inferType g
                          -- shared-first-arg = row; shared-second = col;
                          -- conclusion must equate the differing args
                          if as1[0]! == as2[0]! && as1[1]! != as2[1]! &&
                              ((e1 == as1[1]! && e2 == as2[1]!) ||
                               (e1 == as2[1]! && e2 == as1[1]!)) then
                            pure (some ⟨.row, 81, 9, ← mkRCGuardLam inTy true⟩)
                          else if as1[1]! == as2[1]! && as1[0]! != as2[0]! &&
                              ((e1 == as1[0]! && e2 == as2[0]!) ||
                               (e1 == as2[0]! && e2 == as1[0]!)) then
                            pure (some ⟨.col, 81, 9, ← mkRCGuardLam inTy false⟩)
                          else pure none
                      | _ => pure none
                | _, _ => pure none
            | _ => pure none
        | _ => pure none
      | _, _, _ => pure none

/-- Is `e` an application headed by fvar `f`? -/
def isFApp (e : Expr) (f : FVarId) : Bool :=
  match e.getAppFn with
  | .fvar fid => fid == f
  | _ => false

/-- Is `e` headed by constant `n` (checked raw; callers `whnf` first)? -/
def isConstHead (e : Expr) (n : Name) : Bool :=
  match e.getAppFn with
  | .const nm _ => nm == n
  | _ => false

/-- Is `e` an `Option.some` application (any number of args)? -/
def isSomeApp (e : Expr) : Bool :=
  match e.getAppFn with
  | .const nm _ => nm == ``Option.some
  | _ => false

/-- Is `e` the value binder `v`? -/
def isValVar (e : Expr) (vfid : FVarId) : Bool :=
  match e with
  | .fvar fid => fid == vfid
  | _ => false

/-- Is `o` an output application at exactly `(r, c)`? -/
def isRCApp (o : Expr) (c : FVarId) (r cc : Expr) : Bool :=
  if !(isFApp o c) then false
  else
    let as := o.getAppArgs
    if as.size != 2 then false
    else as[0]! == r && as[1]! == cc

/-- Check `e` is `Eq x y` up to order. -/
def isEqPair (e x y : Expr) : Bool :=
  if !(isConstHead e ``Eq) then false
  else
    let as := e.getAppArgs
    if as.size != 3 then false
    else ((as[1]! == x && as[2]! == y) || (as[1]! == y && as[2]! == x))

/-- Classify a 9×9 box conjunct
`∀ r₁ c₁ r₂ c₂, boxGuard → valGuard → idxEq ∧ idxEq` into a
guarded-≠ frag over `Fin 81` via `boxGuardLin`. All work happens
inside the telescope (so `boxB` can close over the live binders);
the user box guard must be pure and `BEq`-comparable, the value
guard must equate the two cells, and the conclusion must equate
the two index pairs. -/
def matchNestedBox (g c : Expr) (cj : Expr) : MetaM (Option Frag) := do
  let cjW ← whnf cj
  forallBoundedTelescope cjW (some 4) fun fvs rest => do
    if fvs.size != 4 then pure none
    else
      let mut ok := true
      for v in fvs do
        match ← finBound (← inferType v) with
        | some 9 => pure ()
        | _ => ok := false
      if !ok then pure none
      else
        match rest with
        | .forallE _ dom1 cod1 _ =>
          if cod1.hasLooseBVars then pure none
          else match cod1 with
          | .forallE _ dom2 cod2 _ =>
            if cod2.hasLooseBVars then pure none
            else
              if dom1.containsFVar c.fvarId! then pure none
              else if dom1.containsFVar g.fvarId! then pure none
              else
                let dom2R ← whnf dom2
                if !(isConstHead dom2R ``Eq) then pure none
                else
                  let dargs := dom2R.getAppArgs
                  if dargs.size != 3 then pure none
                  else
                    let v1 := dargs[1]!
                    let v2 := dargs[2]!
                    let vvOk : Bool :=
                      (isRCApp v1 c.fvarId! fvs[0]! fvs[1]! &&
                        isRCApp v2 c.fvarId! fvs[2]! fvs[3]!) ||
                      (isRCApp v1 c.fvarId! fvs[2]! fvs[3]! &&
                        isRCApp v2 c.fvarId! fvs[0]! fvs[1]!)
                    if !vvOk then pure none
                    else
                      let codR ← whnf cod2
                      if !(isConstHead codR ``And) then pure none
                      else
                        let cargs := codR.getAppArgs
                        if cargs.size != 2 then pure none
                        else
                          let k1W ← whnf cargs[0]!
                          let k2W ← whnf cargs[1]!
                          let ccOk : Bool :=
                            (isEqPair k1W fvs[0]! fvs[2]! &&
                              isEqPair k2W fvs[1]! fvs[3]!) ||
                            (isEqPair k1W fvs[1]! fvs[3]! &&
                              isEqPair k2W fvs[0]! fvs[2]!)
                          if !ccOk then pure none
                          else
                            -- user condition as `boxB` via `==`
                            -- (no `Decidable` synthesis on fvars)
                            let d1args := (← whnf dom1).getAppArgs
                            if d1args.size != 3 then pure none
                            else
                              let blhs := d1args[1]!
                              let brhs := d1args[2]!
                              let beqB ← mkAppM ``BEq.beq #[blhs, brhs]
                              let boxB ← mkLambdaFVars
                                #[fvs[0]!, fvs[1]!, fvs[2]!, fvs[3]!] beqB
                              if boxB.hasLooseBVars then pure none
                              else
                                let inTy ← inferType g
                                let fin81 := mkApp (mkConst ``Fin []) (mkNatLit 81)
                                withLocalDeclD `gin inTy fun gin =>
                                withLocalDeclD `ii fin81 fun ii =>
                                withLocalDeclD `jj fin81 fun jj => do
                                  let app ← mkAppM
                                    ``Lynth.Sat.Compile.boxGuardLin #[boxB, ii, jj]
                                  let gl ← mkLambdaFVars #[gin, ii, jj] app
                                  pure (some ⟨.box, 81, 9, gl⟩)
          | _ => pure none
        | _ => pure none

/-- Classify a givens conjunct `∀ r c v, optGuard → outEq-to-v`
into a forced-value frag over `Fin 81 × Fin 9` via `givenGuardLin`.
All work happens inside the telescope (so `givB` can close over
the live binders); the input guard must not mention the output
and must be `BEq`-comparable, and the conclusion must equate the
output at `(r, c)` with `v`. -/
def matchNestedGiven (g c : Expr) (cj : Expr) : MetaM (Option Frag) := do
  let cjW ← whnf cj
  forallBoundedTelescope cjW (some 3) fun fvs rest => do
    if fvs.size != 3 then pure none
    else
      let mut ok := true
      for v in fvs do
        match ← finBound (← inferType v) with
        | some 9 => pure ()
        | _ => ok := false
      if !ok then pure none
      else
        match rest with
        | .forallE _ dom cod _ =>
          if cod.hasLooseBVars then pure none
          else
            let domR ← whnf dom
            if !(isConstHead domR ``Eq) then pure none
            else if domR.containsFVar c.fvarId! then pure none
            else
              let dargs := domR.getAppArgs
              if dargs.size != 3 then pure none
              else
                let a := dargs[1]!
                let b := dargs[2]!
                let optSide : Option (Expr × Expr) :=
                  if isFApp a g.fvarId! && isSomeApp b then some (a, b)
                  else if isFApp b g.fvarId! && isSomeApp a then some (b, a)
                  else none
                match optSide with
                | none => pure none
                | some (_, someApp) =>
                  let sargs := someApp.getAppArgs
                  if sargs.size != 2 then pure none
                  else if !(isValVar sargs[1]! fvs[2]!.fvarId!) then pure none
                  else
                    let inApp := match optSide with
                      | some (ia, _) => ia
                      | none => a
                    let iargs := inApp.getAppArgs
                    if iargs.size != 2 then pure none
                    else if !(iargs[0]! == fvs[0]! && iargs[1]! == fvs[1]!) then
                      pure none
                    else
                      let codR ← whnf cod
                      if !(isConstHead codR ``Eq) then pure none
                      else
                        let cargs := codR.getAppArgs
                        if cargs.size != 3 then pure none
                        else
                          let o1 := cargs[1]!
                          let o2 := cargs[2]!
                          let outOk : Bool :=
                            (isFApp o1 c.fvarId! && isValVar o2 fvs[2]!.fvarId! &&
                              isRCApp o1 c.fvarId! fvs[0]! fvs[1]!) ||
                            (isFApp o2 c.fvarId! && isValVar o1 fvs[2]!.fvarId! &&
                              isRCApp o2 c.fvarId! fvs[0]! fvs[1]!)
                          if !outOk then pure none
                          else
                            -- input condition as `givB` via `==`
                            let lhsG := dargs[1]!
                            let rhsG := dargs[2]!
                            let beq0 ← mkAppM ``BEq.beq #[lhsG, rhsG]
                            let givB ← mkLambdaFVars
                              #[g, fvs[0]!, fvs[1]!, fvs[2]!] beq0
                            if givB.hasLooseBVars then pure none
                            else
                              let inTy ← inferType g
                              let fin81 := mkApp (mkConst ``Fin []) (mkNatLit 81)
                              let fin9 := mkApp (mkConst ``Fin []) (mkNatLit 9)
                              withLocalDeclD `gin inTy fun gin =>
                              withLocalDeclD `ii fin81 fun ii =>
                              withLocalDeclD `vv fin9 fun vv => do
                                let app ← mkAppM
                                  ``Lynth.Sat.Compile.givenGuardLin
                                  #[inTy, givB, gin, ii, vv]
                                let gl ← mkLambdaFVars #[gin, ii, vv] app
                                pure (some ⟨.given, 81, 9, gl⟩)
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
`gin` is the input fvar. Bounds come from the fragment itself. -/
def mkFamBody (fr : Frag) (gin : Expr) : MetaM Expr := do
  let kk := mkNatLit fr.k
  match fr.kind with
  | .inj =>
    -- complete difference with a decidable diagonal guard
    withLocalDeclD `i (finTyLit fr.n) fun i =>
    withLocalDeclD `j (finTyLit fr.n) fun j => do
      let ne ← mkAppM ``Ne #[i, j]
      let gd ← mkDecide ne
      let piece ← mkAppM ``Lynth.Sat.Differ.condDiffPair
        #[kk, ← finValOf i, ← finValOf j, gd]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit fr.n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit fr.n
      flatMapApp ri lamI
  | .req =>
    withLocalDeclD `i (finTyLit fr.n) fun i =>
    withLocalDeclD `v (finTyLit fr.k) fun v => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condUnitNeg
        #[kk, ← finValOf i, ← finValOf v,
          mkAppN fr.guard #[gin, i, v]]
      let lamV ← mkLambdaFVars #[v] piece
      let rv ← finRangeLit fr.k
      let inner ← flatMapApp rv lamV
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit fr.n
      flatMapApp ri lamI
  | .ne | .row | .col | .box =>
    -- guarded difference: rows/cols/boxes share the shape, only
    -- their (prebuilt) guards differ
    withLocalDeclD `i (finTyLit fr.n) fun i =>
    withLocalDeclD `j (finTyLit fr.n) fun j => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condDiffPair
        #[kk, ← finValOf i, ← finValOf j,
          mkAppN fr.guard #[gin, i, j]]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit fr.n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit fr.n
      flatMapApp ri lamI
  | .eq =>
    withLocalDeclD `i (finTyLit fr.n) fun i =>
    withLocalDeclD `j (finTyLit fr.n) fun j => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condEqPair
        #[kk, ← finValOf i, ← finValOf j,
          mkAppN fr.guard #[gin, i, j]]
      let lamJ ← mkLambdaFVars #[j] piece
      let rj ← finRangeLit fr.n
      let inner ← flatMapApp rj lamJ
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit fr.n
      flatMapApp ri lamI
  | .given =>
    -- forced values over index/value pairs
    withLocalDeclD `i (finTyLit fr.n) fun i =>
    withLocalDeclD `v (finTyLit fr.k) fun v => do
      let piece ← mkAppM ``Lynth.Sat.Differ.condUnitPos
        #[kk, ← finValOf i, ← finValOf v,
          mkAppN fr.guard #[gin, i, v]]
      let lamV ← mkLambdaFVars #[v] piece
      let rv ← finRangeLit fr.k
      let inner ← flatMapApp rv lamV
      let lamI ← mkLambdaFVars #[i] inner
      let ri ← finRangeLit fr.n
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
    fams := fams ++ [← mkFamBody fr gin]
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

/-- Closed nested decoder `Assignment → Fin 9 → Fin 9 → Fin 9`
through the linear decoder. -/
def mkDecodeNested (hk : Expr) : MetaM Expr := do
  withLocalDeclD `m (← assignTy) fun m =>
  withLocalDeclD `r (finTyLit 9) fun r =>
  withLocalDeclD `c (finTyLit 9) fun c => do
    let cell := mkApp (mkApp (mkConst ``Lynth.Sat.Compile.lin2D []) r) c
    let d ← mkAppM ``Lynth.Sat.FinVal.decodeVal
      #[mkNatLit 81, mkNatLit 9, hk, m, cell]
    mkLambdaFVars #[m, r, c] d

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
  else do
    let right ← mkAppM ``And.right #[hPf]
    conjProj right (idx - 1) (total - 1)

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

/-- Nested 9×9-board path: all conjuncts classify as nested
fragments sharing dims `[9,9] → 9`. -/
def matchFragNested (P : Expr) : MetaM (Option (List Frag)) := do
  let PR ← whnf P
  lambdaTelescope PR fun lams bodyLam => do
    if lams.size != 2 then pure none
    else
      let g := lams[0]!
      let c := lams[1]!
      match ← finDimsTy (← inferType c) with
      | some ([9, 9], 9) =>
        -- unfold `ValidSolution` etc. before splitting
        let bodyW ← whnf bodyLam
        let mut frags : List Frag := []
        for cj in splitConj bodyW do
          let cjW ← whnf cj
          match ← matchNestedConj g c cjW with
          | some fr => frags := fr :: frags
          | none =>
            match ← matchNestedBox g c cjW with
            | some fr => frags := fr :: frags
            | none =>
              match ← matchNestedGiven g c cjW with
              | some fr => frags := fr :: frags
              | none => return none
        pure (some frags.reverse)
      | _ => pure none


/-- Single-level fragment path (v1 bodies). -/
def matchFrag1D (P : Expr) : MetaM (Option (List Frag)) := do
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
                  else do
                    let b0 ← finBound (← inferType fvs[0]!)
                    let b1 ← finBound (← inferType fvs[1]!)
                    match b0, b1 with
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


/-- Fragment entry: 1D shapes first, nested boards second. -/
def matchFrag (P : Expr) : MetaM (Option (List Frag)) := do
  match ← matchFrag1D P with
  | some frags => pure (some frags)
  | none => matchFragNested P

end Lynth.Sat.Compile
