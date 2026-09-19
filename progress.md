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
- Lean-term denotes link for certificates (translation trusted +
  fuzz-tested; kernel re-check is the safety net).
- Full MBQI blocked (open-term evaluation over infinite domains);
  only decidable finite fragments are in reach.
- No CDCL(T)/Nelson-Oppen loop by design (SPEC: sequential
  explanation-passing instead).
- `SPEC.md` working-tree reformatting uncommitted — review before
  committing.
