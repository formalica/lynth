# lynth progress

Living status snapshot. Update on each tick: move finished items to
"Done", keep "Next" pointing at the lowest unfinished `TASKS.md` item.
Direction lives in `SPEC.md`; backlog lives in `TASKS.md`.

## HEAD

- Commit `7e39061` — SPEC: iterative solving, procedure=theory renaming,
  goal enrichment.
- Tree status: CDCL(T) lazy expansion implemented, all 32 suites green
  (staged below, uncommitted).

## Done (merged, green)
- `lynth` tactic + 6-procedure dispatcher
  (`witness → euf → ring → sat → arith → nlin`), per-procedure failure
  notes in the final error.
- `Witness`: `Subtype`/`Exists` over `Nat`/`Int`/`Bool`/`Prod`/`Fin n`;
  enumeration + bound-directed starts (equality extraction, lower bounds).
- `EUF`: equality graph, congruence fixpoint (`congr` chains),
  `Ne`/`False` close by contradiction; `shareDerived` asserts proven
  equalities for later procedures.
- `Quant` (Q1): E-matching ground instantiation over EUF classes
  (`Trigger.matchMod` syntactic + canon-validated); proven instances
  asserted, procedure always yields.
- `Arrays` (Q2): read-over-write R1/R2 with core-lemma proofs
  (`Array.getElem_set_self/ne`), bound/`≠` premises by scan + decide.
- `Datatypes` (Q3): injectivity splintering + discrimination via core
  bounded `injections`; enrich-and-yield, zero axioms.
- `BV` (Q4): Tseitin bit-blast (ripple-carry) + CDCL validity oracles,
  bidirectional fuzz vs brute force; `bv_decide` closes.
- `Arith/Farkas` (Q5): Simplex row lineage + validated `DdMExplanation`s.
- `FinSearch` (Q6 core): finite-function synthesis (`Lynth/FinSearch/`).
  Detector + router (`Detect.lean`: cardinality estimate, named
  cell/CNF/fuel thresholds, kernel-checked routing tests); constraint
  recognizer (`Eq`/`Ne`/`LT`/`LE`/`And`/`Or`/`Not`/`Iff`/bounded-`∀`
  unrolling/`List.Pairwise`/`Fintype.card`-subtype counting over
  `Fin n`/`Bool`); one-hot + Tseitin CNF encoder with differential
  fuzz vs brute force (`Test/FinFuzz.lean`, 0 mismatches incl. `exactK`
  edge counts); CDCL SAT child decoding closed `fun` + `List.getD`
  value terms, verified by `decide` (user predicates unfolded,
  current-module only). Pilots `Test/FinSearch.lean`: 4×4 Sudoku
  (`[propext]`), 4×4 Towers with order + counting clues
  (`[propext, Classical.choice, Quot.sound]`), scalar routing to
  `Witness`. Runs first in `Frontend.dispatch`, yields gracefully.
- `Ring` (`ring`), `Nlin` (`nlinarith`) kernel-checked normalizers.
- `Sat`: watched-literal CDCL core (`Watch.lean`, native CreuSAT port:
  2WL + blockers + circular search, VMTF, phase saving, array state,
  `checkSat` gate) with first-UIP traces + backjump + geometric
  restarts; differential fuzz vs DPLL at 0 mismatches (small + larger
  mixed shapes with units) + trace validation + watch-scan regression
  test; full Star Battle now 5s (was 300s+ timeout), 9×9 Sudoku ~8s
  (was 2.5min: VMTF init-order sort had thousands of tied keys →
  pathological `Array.qsort` partitioning; fixed with a
  `(count, var-id)` tie-break comparator + regression note in
  `Test/CdclFuzz.lean`; `checkSat` model gate switched from per-literal
  list `lookup` to one array pass).
  Soundness bug caught by pilots during the port (inverted circular
  scan args → spurious level-0 conflicts) fixed + regression-locked.
- `FinSearch` generic finite types (no `Option` hardcoding): `finCard`
  by constructor inspection (non-recursive, non-indexed inductives
  over finite fields — `Option`/`Sum`/`Prod`/enumerations; `isRec` +
  sibling-occurrence + dependent-field rejection), `exprToIdx` /
  `finValExpr` value layout shared by recognizer and reconstruction,
  closed-term folding (user defs like `box_idx`, partial-board
  `match`es evaluate to literals instead of opaque cells),
  kernel-evaluation folding at default transparency (`withReducible`
  left `decide` stuck on user defs), vacuous-implication
  short-circuit (9⁴ box instances fit the CNF budget), generic
  `domOf`/`valLit`/binder indexing (`BEq` cond-chains, computable).
  Pilots: user-formalized Inkala 2012 9×9 (`Test/Sudoku9Inkala.lean`,
  injective rows/cols + `box_idx` + `Option` partial board, ~48s,
  `[propext]`), partial-board 9×9 (`Test/Sudoku9Partial.lean`,
  `[propext]`), alternative 4×4 shapes (`Test/FinSearchAlt.lean`:
  quantified implications, `Fintype.card` counts, `Iff` links).
- `Arith`: FM elimination (Farkas lineage + validation), tableau
  Simplex (DdM, models), branch-and-bound; exact `Int`/`Nat`
  translation; FM-vs-Simplex differential clean.
- Proved, native-axioms-only: `FarkasSound.farkas_sound`,
  `checkCert_sound`; reconstruction statements in
  `Lynth/Certificates.lean` (zero `axiom`s, zero `sorry`s repo-wide).
- Docs: real `README.md` (executable via `Test/Readme.lean`),
  `DESIGN.md`, `PROCEDURES.md` (theories-as-procedures registry),
  `docs/Z3-NOTES.md` (pinned Z3 `d5d9266`); `TASKS.md` backlog + loop
  driver; CI runs all 20 `Test/*.lean` suites.

## Next (lowest unfinished first)

- `TASKS.md#Q7` — DRAT emission for the SAT core (traces already
  recorded + validated; needs standard clause-ID/deletion emission).
- Then Q9 combination feedback, Q10 chained instantiation,
  Q11 BV operators, Q12 nested arrays, Q13 datatype selectors;
  Q14 is the recurring regression watch. (Q8 watched literals done
  via the CreuSAT-ported engine; EMA restarts + clause-DB reduction
  remain as optional follow-ups.)
- Q6 scale pilots DONE this tick: 9×9 SudokuPartial closes end to end
  (~38s, axioms `[propext]`); see Done entry below.
- `listsynth` batch (this tick): `Test/FinDomain` pilots
  ReverseMapChain, EraseReplacePreimage, SubsetSum, SortPerm close
  end to end (3–4s each; TakeDropExact still green) via shared
  `ListInfer` extensions only — relation questions for non-`Eq`
  props (`Sublist`/`Perm` reference domains), peel questions for
  nested calls, definition-unfolding closed readers, new
  erase/replace/sublist/perm dispatch rows, sublist enumeration,
  sorted-first plus bounded pool products over length windows,
  widened-pool retry. SubsetSum/SortPerm pin
  `[propext, Classical.choice, Quot.sound]` (Perm/Sublist
  decidability, same precedent as StarBattle10x10). Remaining
  FinDomain pilots still yield gracefully (SafetyInvariant breaks
  in its own `omega`, pre-existing).

## Open gaps / risks (honest list)

- Q6 scale pilots: `Test/StarBattle.lean` now uses a 9×9 board with one
  star per row/column/3×3 region and no touching, including diagonals.
  Three clean end-to-end runs: 5.314s, 5.109s, 5.301s; axioms
  `[propext, Classical.choice, Quot.sound]`. Counting recognition now
  permits width 9; balanced conjunctions and a local instance-synthesis
  size budget keep reconstruction within limits. This is a regular-region,
  one-star pilot, not an irregular-region/two-star benchmark.
  9×9 Sudoku (`Test/Sudoku9.lean`) remains ~6s after the qsort tie-break fix.
  All 29 suites pass; CDCL and finite-encoder fuzz report zero mismatches.
- Q6 9×9 direttissima (this tick): `Test/Sudoku9Partial.lean` (user's
  `Idx`/`Val` formalization, `eraseDups`-based no-dups) closes end to
  end in ~38s with axioms `[propext]`, via lazy CDCL(T) expansion
  (`Lynth/FinSearch/Theory.lean`): big pieces stay out of the CNF as
  opaque atoms (split by node count + cell-disjointness + atom-yield
  lookahead, single bottom-up pass); the SAT solver proposes
  candidates over the small base and each failure teaches blocking
  clauses (certified duplicate pairs generalized over values, greedy
  fallback). Soundness split unchanged: search untrusted, kernel
  `decide` re-verifies every model; learned clauses can only rule out
  non-solutions. `Test/Sudoku9.lean` stays ~6s eager; Inkala ~41s.
- StarBattle `sorryAx` diagnosis (this tick): the `sorryAx` was a
  symptom, not a tactic bug — when `lynth` failed to close the goal,
  Lean stubbed the declaration with `sorry`. The underlying failure
  (top-level `and[4029,569]` fused into one counting-meaning atom,
  then unsound pair-learning deriving UNSAT) was already fixed by the
  zero-yield eager rule. Test now passes stably (~5s, 4 consecutive
  runs) with axioms `[propext, Classical.choice, Quot.sound]` and
  carries the same `guard_msgs` pin as the other suites.
- Lean-term denotes link for certificates (translation trusted +
  fuzz-tested; kernel re-check is the safety net).
- Full MBQI blocked (open-term evaluation over infinite domains);
  only decidable finite fragments are in reach.
- No CDCL(T)/Nelson-Oppen loop by design (SPEC: sequential
  explanation-passing instead).
- `SPEC.md` working-tree reformatting uncommitted — review before
  committing.
- `lynth_grind` wrapper-first (this tick): the 184-file grind port
  (`Lynth/Grind`) compiles but could not run — every goal died in the
  IR interpreter, first as an assertion violation (`ir_interpreter.cpp:928`),
  finally diagnosed as missing native implementations of the C++-only
  `@[extern]` kernels (`preprocess`, `internalize`, `mkEqProof`, cutsat
  helpers, …): `lake env lean` never loads our native objects, while the
  toolchain resolves the same symbols for core grind. Interpreted-safe
  fixes applied to the port (`initialize` for `builtin_initialize`,
  incl. the two `lynth_grind.*` options; plain `def`+`simproc_pattern%`
  for `builtin_simproc_decl` (one `dsimproc [simp,seval]` global-attr
  registration dropped — `lynth_grind` still picks it up via explicit
  `addSimproc`); base simp set read from core `normExt`; a
  `simproc_pattern%` line rescued from inside a `/-!` block). The tactic
  entry (`Lynth/Grind/Tactic.lean`) now elaborates our syntax/config and
  delegates to the core engine, so `lynth_grind` has full `grind` parity
  (EUF/arith/prop goals, `only`/params) and `lynth_grind?` reports
  `lynth_grind only …` suggestions (core `grind?` node rebuilt through
  our quotation; its `throwUnsupportedSyntax`-on-foreign-kind was the
  last "Unexpected syntax" red herring). `lake build` clean (18025
  jobs), all 33 `Test/*.lean` green, FinDomain 5/5 expected passes.
  TODO: feed `@[lynth_grind]` theorems as extra params, wire as a
  `lynth` procedure, adapt upstream grind tests.
- Upstream grind tests (this tick): copied the lean4 grind corpus
  (421 files: `tests/elab/grind_*`, `tests/lean/grind/`) into
  `Test/Grind/`, adapted by script (`grind`→`lynth_grind`,
  `grind?`→`lynth_grind?` outside strings/comments/docstrings;
  `@[grind]` attrs, `trace[grind]`, `set_option grind.*`, message texts
  stay core since the tactic delegates). Excluded: `sorry` files (repo
  ban), `grind!`/`sym`/`grind_order` (not ported), Mathlib imports,
  `#exit` stubs. Triage fixed three adaptation bugs (compound-attr
  rename crashing on our attr, guard-docstring corruption, suggestion
  naming incl. nested `<;>` kept as core text) and adopted the harness
  flags (`-Dlinter.all=false -DElab.inServer=true`). 12 files dropped
  as unadaptable (core `grind` fails identically in-repo on 7 heavy
  algebra files — env search shift, not a delegation gap; anchor/wrap/
  pretty-print drift on 4; `exact?` integration on 1). Final: 100/100
  green, incl. 12 `lynth_grind?` suggestion files. Docs in
  `Test/Grind/README.md` + `MANIFEST.txt`.
- Grind tests finale (this tick): fixed the last 4 red files by pinning
  environment-true expected texts (suggestion re-wrap ×2, stable anchors
  ×1, qualified pretty-print ×1) after proving each diff was
  naming-only; `try?`-produced core suggestions correctly stay bare
  `grind`. Skipped 8 (7 heavy algebra files where core `grind` fails
  identically in-repo — swap-proven environmental, plus the `exact?`
  integration test). Final: 293/293 green, split `Test/Grind/Fast/`
  (285, ≤10s) + `Test/Grind/Slow/` (8, >10s) by measured wall-clock,
  run with the harness flags (`-Dlinter.all=false -DElab.inServer=true`).
- E-graph procedure (this tick): new `Lynth/Egraph/Procedure.lean` drives
  the core e-graph as a library (zero grind code copied — `GrindM.runAtGoal`
  + `processHypotheses` + split-free `solvers <|> instantiate` saturation,
  VCGen-precedented), wired after `euf` in dispatch. Exports `newFacts`
  plus congruence-class equalities via core `mkEqProof`, oriented
  big-to-small (equal-size atomic kept, compound skipped) so downstream
  `simp` terminates; harvested `False` refutes; forwarder-mvar rollback
  keeps it footprint-free. Two hazards found and fixed along the way:
  `initCore`'s `transformTarget` forwarder faking empty goals (bogus
  "refutation" + kernel holes), and unoriented exports looping `simp`
  (5 suites). One deliberate pin change: `dt_discr_false` []→[propext]
  (egraph refutation supersedes the axiom-free datatypes path).
  Full suite green (33/33), FinDomain 5/29 unchanged; pilots need
  per-pilot diagnosis next.
- Answer goals + first pilot flips (this tick): new `Lynth/Answer/Procedure`
  splits `Sum`/`PSum` goals (the FinDomain `Answer` shape) — right branch
  tries finite `decide` refutation under a domain-cardinality guard
  (`Fintype.card` evaluated by `whnf`, max 100000; unfolds head defs via
  euf's `collectSubterms`), else intros + egraph refutation; left branch
  refines `inl` and runs the synthesis sub-pipeline. Debugging lessons:
  `mkAppM` leaves `Fintype` instances unsynthesized (explicit levels +
  explicit `synthInstance` needed, off-by-one: `Fintype.{u}` takes
  `Type u`), `simp only [defs]` splice ill-typed for this use (plain
  `unfold` instead). Full core `grind` provably cannot refute K4 (no
  pigeonhole) — enumeration is the right engine. Flips both 3-coloring
  pilots (Sat via synthesis, Unsat via decide; Unsat pin set to the
  SubsetSum precedent `[propext, Classical.choice, Quot.sound]`).
  Full suite green (33/33), FinDomain 7/29; remaining 22 need per-pilot
  diagnosis next.
- FinDomain campaign (ongoing, 17/29): `listsynth` gained comparison
  length bounds (`≤`/`<`/`≥`/`>` over `length`, both `LE`/`LT` and
  `Nat.le`/`Nat.lt` elaborations), `List (Fin n)` enumeration, `List.all`
  bound pools, default length caps from small pools, and a kernel
  `decide`-eval fast path (`DecidablePred` once); `witness` gained
  finite-function tables, single-ctor structures, full-product pairing,
  and `closeSide` moved here with fast-reject + unfold-hoisting +
  `Sublist`-optimality fallback (`simp only [←mem_sublists]`+`decide`).
  Flipped since last commit: TogglePlan, ExactCover, GraphIso,
  NimStrategy (`[propext, Quot.sound]`), FilterPartitionCount,
  SafetyInvariant (broken `omega` in spec repaired),
  Nonogram (broken `runs` termination repaired), DfaLearn,
  MinSubsetExceed (`[propext, Quot.sound]`). Debugging lessons:
  `List.length` carries its implicit type arg (match on `getAppFn`);
  `restoreState` erases post-snapshot logs (use return-value probes);
  tactic quotations need their theorems imported (`Mathlib.Data.List.
  Sublists`); `whnf` on `Fintype.card` builds huge `Finset.univ`.
  Remaining 12 need bigger machinery each (see next ticks).
- Debugging lessons (MinSubsetExceed campaign, expensive): (1)
  `restoreState` truncates the message log back to the snapshot, so
  `logInfo` inside snapshot regions vanishes on restore — observe via
  return values or logs placed outside snapshots, never inside.
  (2) Tactic syntax quotations mentioning Mathlib theorems
  (`simp only [←List.mem_sublists]`) need the home module imported
  (`Mathlib.Data.List.Sublists`), else `simp` fails silently at
  runtime while the definition still compiles. (3) When observed
  behavior contradicts source, verify olean freshness (timestamps +
  string grep) before theorizing — stale builds plus (1) compound.
  (4) After scripted file surgeries (python/sed), always re-read the
  edited region (`git diff`): this tick lost hours to a duplicated
  def, a split docstring, and a diagnostic stub left in place.
- More pilots (17/29): Nonogram (broken `runs` termination repaired +
  raised Pi cap), DfaLearn (structure synthesis: field-order bug fixed),
  MinSubsetExceed (optimality fallback `simp only [←mem_sublists]` +
  `decide`, needs the `Mathlib.Data.List.Sublists` import for quotation
  scope; pin `[propext, Quot.sound]`). Full verification each round:
  33/33 Test, 293/293 Grind, 17/29 FinDomain. Remaining 12 need bigger
  machinery each: FinGroup (constraint propagation/SAT binary),
  Cryptarithm + queens (arithmetic in SAT encoding), ShortestPath
  (length-bounded completeness), SplitRejoin/SortingNetwork (product
  domains), IdxFind (positional), KnightsTour (binary SAT at scale),
  TwoGuards (higher-order + Equivs), BalancedBST (custom inductive),
  DistanceCode (nested lists).
