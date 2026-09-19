import Lynth.FinSearch.Syntax

/-!
Lazy theory layer for the finite-domain procedure (CDCL(T) shape):
big constraint pieces stay out of the CNF as opaque `atom`s, the SAT
solver proposes candidates, and failures come back as small blocking
clauses over the cells that actually caused them.

Nothing here knows any puzzle or any list function: the split cuts
by node count *and cell-disjointness* (see `splitPos`), and
explanations are minimized by re-evaluating the piece itself
(`evalProp`) on varied assignments. Anything learned is implied by
the original piece, so learning can only rule out non-solutions;
the kernel still re-verifies the final model.
-/
namespace Lynth.FinSearch.Theory

open Lynth.FinSearch

/-- Pieces bigger than this stay out of the CNF. A single
`has_no_dups` over 9 symbolic cells is ~21k nodes; ordinary
equalities are a handful of nodes, so anything in the low thousands
cleanly separates eager from lazy. -/
def lazyThreshold : Nat := 2000

/-- Splitter state: collected opaque pieces. -/
abbrev SplitM := StateM (Array FProp)

/-- Opaque a piece: stash it and return its atom reference. -/
def atomize (p : FProp) : SplitM FProp := do
  let atoms ← get
  set (atoms.push p)
  pure (.atom atoms.size)

/-- Bottom-up summary of a subtree: node count, deduped cell ids,
whether it splits into independent big pieces, and how many opaque
atoms splitting it would produce. Computed once per node in a
single pass (see `annotate`). -/
structure Info where
  size : Nat
  cells : List Nat
  splittable : Bool
  nyield : Nat
deriving Inhabited

/-- Annotated proposition: the original node plus its summary plus
annotated children (parallel to the original's children; empty for
leaves and for non-`and`/`not` nodes, which the splitter never
descends into). -/
structure AProp where
  orig : FProp
  info : Info
  kids : List AProp

instance : Inhabited AProp := ⟨⟨.tru, default, []⟩⟩

/-- Cells of a term. -/
def termCells : FTerm → List Nat
  | .var _ a => [a]
  | .lit _ _ => []

/-- Union of deduped cell lists. -/
def unionCells : List Nat → List Nat → List Nat
  | [], ys => ys
  | x :: xs, ys => if x ∈ ys then unionCells xs ys else x :: unionCells xs ys

/-- Info for a leaf-ish node (no splittable children): big pieces
yield one atom, small pieces none. -/
def leafInfo (size : Nat) (cells : List Nat) : Info :=
  { size, cells, splittable := false,
    nyield := if size > lazyThreshold then 1 else 0 }

/-- Are these sibling cell-sets pairwise disjoint? A single child
is vacuously disjoint. -/
def disjointCells : List (List Nat) → Bool
  | [] => true
  | cs :: rest =>
    if cs.any (· ∈ rest.foldl unionCells []) then false
    else disjointCells rest

/-- Single bottom-up annotation pass: one visit per node. Sizes,
cell sets, splittability and yields are all assembled from the
children's summaries, so no subtree is ever re-walked (the old
code called `propSize`/`collectCells`/`splittable`/`yield`
repeatedly per level, and evaluated `yield`'s child list twice per
node — exponential on deep conjunction chains). -/
partial def annotate : FProp → AProp
  | p@(.eq a b) =>
    ⟨p, leafInfo 1 (unionCells (termCells a) (termCells b)), []⟩
  | p@(.ne a b) =>
    ⟨p, leafInfo 1 (unionCells (termCells a) (termCells b)), []⟩
  | p@(.distinct ts) =>
    ⟨p, leafInfo (1 + ts.length)
      (ts.foldl (fun acc t => unionCells acc (termCells t)) []), []⟩
  | p@(.lt a b) =>
    ⟨p, leafInfo 1 (unionCells (termCells a) (termCells b)), []⟩
  | p@(.le a b) =>
    ⟨p, leafInfo 1 (unionCells (termCells a) (termCells b)), []⟩
  | p@(.tru) => ⟨p, leafInfo 1 [], []⟩
  | p@(.fls) => ⟨p, leafInfo 1 [], []⟩
  | p@(.atom i) => ⟨p, leafInfo 1 [], []⟩
  | p@(.or ps) =>
    let kids := ps.map annotate
    let size := 1 + (kids.foldl (fun n k => n + k.info.size) 0)
    let cells := kids.foldl (fun acc k => unionCells acc k.info.cells) []
    ⟨p, leafInfo size cells, []⟩
  | p@(.exactK ps _) =>
    let kids := ps.map annotate
    let size := 1 + (kids.foldl (fun n k => n + k.info.size) 0)
    let cells := kids.foldl (fun acc k => unionCells acc k.info.cells) []
    ⟨p, leafInfo size cells, []⟩
  | p@(.not q) =>
    let k := annotate q
    let size := 1 + k.info.size
    ⟨p, leafInfo size k.info.cells, [k]⟩
  | p@(.and ps) =>
    let kids := ps.map annotate
    let size := 1 + (kids.foldl (fun n k => n + k.info.size) 0)
    let cells := kids.foldl (fun acc k => unionCells acc k.info.cells) []
    let big := kids.filter fun k => k.info.size > lazyThreshold
    let splittable :=
      (big.length ≥ 2 && disjointCells (big.map (·.info.cells))) ||
        big.any (·.info.splittable)
    let nyield := (kids.map (·.info.nyield)).sum
    let info : Info :=
      { size, cells, splittable,
        nyield := if splittable || nyield == 0 then nyield else 1 }
    ⟨p, info, kids⟩

mutual
/-- Rewrite the negative side (under `not`): structure preserved,
never opaqued (the loop only enforces positive pieces). Uses the
cached annotation; no recomputation. -/
partial def rewriteNeg : AProp → SplitM FProp
  | ⟨.and _, _, kids⟩ => return .and (← kids.mapM rewriteNeg)
  | ⟨.not _, _, [k]⟩ => return .not (← rewritePos k)
  | ⟨p, _, _⟩ => pure p

/-- Rewrite the positive side. Splittable conjunctions (rows,
columns, boxes over disjoint cells) rebuild piece by piece, so each
semantic unit becomes its own atom. Anything big that does not
split (tangled case debris over shared cells) atomizes whole, so
minimization always sees coherent single-condition pieces.
Small conjunctions rebuild as-is (eager hygiene). All decisions
read the cached annotation. -/
partial def rewritePos : AProp → SplitM FProp
  | ⟨.and _, info, kids⟩ =>
    -- Separable big pieces rebuild independently (one atom per
    -- row/column/box). A tangled big conjunction fuses whole (its
    -- case-branches only minimize sanely together). But when
    -- recursing would yield no atoms at all (big only because many
    -- small pieces add up, like counting constraints), stay eager:
    -- fusing smalls into an atom gains nothing and invites unsound
    -- pair-learning on non-pair-sustained meanings.
    if info.splittable || (kids.map (·.info.nyield)).sum == 0 then
      return .and (← kids.mapM rewritePos)
    else
      atomize (FProp.and (kids.map (·.orig)))
  | ⟨.not _, _, [k]⟩ => return .not (← rewriteNeg k)
  | ⟨p, info, _⟩ => do
    if info.size > lazyThreshold then
      atomize p
    else pure p
end

/-- Top-level split: base proposition (small, goes to CNF) plus the
opaque pieces in atom-id order. Empty atoms means the eager path. -/
def splitLazy (p : FProp) : FProp × Array FProp :=
  let (base, atoms) := StateT.run (rewritePos (annotate p)) #[]
  (base, atoms)

/-- Cap on lazy-loop rounds. Every round learns at least one new
clause ruling out the current candidate, so the loop always makes
progress; this is only a backstop against pathological chatter. -/
def maxIters : Nat := 2000

/-- Value generalization for a duplicate-pair core: which values
`v` keep the piece false when both cells take `v` (others at
`vals`)? Learned as one blocking clause per passing value, so a
single duplicate teaches the full disequality instead of one
value-combo. Same fixed-context caveat as greedy (failures are
yields, never wrong proofs); for single-condition pieces like
no-duplicates rows every value passes. -/
def generalizePair (atom : FProp) (i j : Nat)
    (vals : Nat → Nat) (card : Nat → Nat) : List Nat :=
  (List.range (card i)).filter fun v =>
    let both : Nat → Nat := fun x => if x == i || x == j then v else vals x
    evalProp atom both (fun _ => false) == false

/-- Assignment that agrees with `fixed` on its cells and falls back
to `vals` elsewhere, except cell `a` forced to `v`. -/
def assignExcept (fixed : List (Nat × Nat)) (vals : Nat → Nat)
    (a : Nat) (v : Nat) : Nat → Nat :=
  fun x =>
    if x == a then v
    else match fixed.find? fun (y, _) => y == x with
      | some (_, w) => w
      | none => vals x

/-- Greedy 1-minimal core: start from every involved cell at its
current value, drop a cell whenever the piece stays false for all
of that cell's values. The surviving cells with their values imply
the piece is false, so blocking them is a sound theory lemma. -/
def minimizeCore (atom : FProp) (cells : List Nat)
    (vals : Nat → Nat) (card : Nat → Nat) : List (Nat × Nat) :=
  let init := cells.map fun a => (a, vals a)
  go init init
where
  go (kept : List (Nat × Nat)) : List (Nat × Nat) → List (Nat × Nat)
    | [] => kept
    | (a, _) :: rest =>
      let others := kept.filter fun (y, _) => y != a
      let removable :=
        (List.range (card a)).all fun v =>
          evalProp atom (assignExcept others vals a v) (fun _ => false) == false
      go (if removable then others else kept) rest

/-- Duplicate-pair-first minimization. Greedy empties on
multi-violation rows (leftover duplicates sustain falsity through
every removal), yielding useless full-row blocks. Instead, scan the
failing assignment for cells sharing a value; for each such pair,
try dropping every other cell (universal single checks with the
pair fixed). The first fully-certified pair wins: same evidence
standard as greedy (fixed-context universal checks), but it never
empties while a duplicate pair exists. Returns `none` when no pair
certifies (caller falls back to plain greedy). Duplicate pairs are
just equal-valued cells in the current assignment — no puzzle
knowledge, and the certification is what makes the lemma. -/
def certifyPair (atom : FProp) (cells : List Nat)
    (vals : Nat → Nat) (card : Nat → Nat) : Option (Nat × Nat) :=
  go allPairs
where
  allPairs : List (Nat × Nat) :=
    cells.foldl (fun (acc : List (Nat × Nat)) a =>
      acc ++ ((cells.filter fun b => decide (a < b) && vals b == vals a).map
        fun b => (a, b))) []
  go : List (Nat × Nat) → Option (Nat × Nat)
    | [] => none
    | (i, j) :: rest =>
      let base := [(i, vals i), (j, vals j)]
      let others := cells.filter fun a => a != i && a != j
      let ok := others.all fun a =>
        let fixed := base ++ ((others.filter fun b => b != a).map fun b => (b, vals b))
        (List.range (card a)).all fun v =>
          evalProp atom (assignExcept fixed vals a v) (fun _ => false) == false
      if ok then some (i, j) else go rest

end Lynth.FinSearch.Theory
