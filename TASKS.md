# lynth task backlog

## Loop driver (read this first, every tick)

Each tick implements exactly one task, unattended:

1. Read `SPEC.md` — it sets the direction; do not lose it.
2. Run `git log --oneline` — committed items are done.
3. Pick the lowest-numbered task below with no corresponding commit.
4. Implement it following its instructions and the repo conventions
   (no `sorry`, no `axiom`; tested proofs; native-axioms-only
   `#print axioms` checks; update `docs/PROCEDURES.md` registry and the
   CI suite list when adding tests).
5. Verify: `lake build` clean and every `Test/*.lean` suite exits 0.
6. Update `progress.md` (move the item to Done, point Next at the
   following item), commit when green (`git add -A`, short message);
   report what was done, test results, and what remains open. Then
   stop — one task per tick. The next tick repeats from step 1, so the
   backlog drains automatically.

Each task is one scheduler tick: bounded scope, verifiable done-condition.
Conventions for every task: no `sorry`/`axiom`, `#print axioms`-checked
tests (native axioms only), `lake build` clean, commit when green.
Loop-friendly one-liners: `implement TASKS.md#<id>, verify, commit`.

## Q1 — `Quant`: E-matching ground instantiation (`Lynth/Quant/`)

**Why first:** biggest reasoning gap; reuses EUF classes; soundness free
(instances are kernel-checked).
- Collect `∀`-hyps (default-kind decls only — see auxDecl lesson in
  `docs/Z3-NOTES.md`), extract trigger subterms from bodies.
- Match triggers against ground terms in goal/context modulo EUF
  congruence classes (`Lynth.Euf` graph); bound matches per round + fuel.
- Assert instances as hyps (proven `hyp arg` terms) for later procedures;
  wire into `Frontend.dispatch` after `euf`.
- Tests `Test/Quant.lean`: single/multi-premise instantiation,
  congruence-modulo matching, no-match fallthrough; add to CI list.
- Done when: new tests green, full suite green, committed.

## Q2 — `Arrays`: read-over-write + extensionality (EUF sub-procedure)

- Extend EUF graph with `select`/`store` nodes; add congruence edges for
  `select (store a i v) i = v`, `i ≠ j → select (store a i v) j = select a j`,
  and `select`-congruence; array extensionality via `Ne`-close path.
- Proofs: `congr`/`Eq.trans` chains like existing EUF; reuse `shareDerived`.
- Tests `Test/Arrays.lean` + CI. Done when green + committed.

## Q3 — `Datatypes`: injectivity + discrimination (EUF sub-procedure)

- Constructor injectivity (`C a = C b → a = b` per arg) and
  discrimination (`C … ≠ D …` for distinct constructors) as derived edges.
- Tests `Test/Datatypes.lean` (Nat/Option/List shapes) + CI.
- Done when green + committed.

## Q4 — `BV`: bit-blasting over the `Sat` core

- Word-level normalizer for fixed-width `BitVec` ops → CNF
  (`Lynth/BV/`); solve via `Cdcl.cdclSolve` (models + traces free).
- Kernel-checked reconstruction of the blast; differential tests vs
  `decide` on random small instances.
- Tests `Test/BV.lean` + CI. Done when green + committed.

## Q5 — Farkas extraction from Simplex + `lynth_farkas` activation — DONE

- Row lineage over initial equations through `Simplex.pivot`
  (`combo_new = (-1/a)·combo`, others add `f·combo`); at UNSAT emit a
  `DdMExplanation` (combo + violated bound + blocking + model), validated
  by `Explain.checkExplanation` (row re-derivation, basic form,
  blocking equalities, positive residual const).
- `FarkasSound.checkCert` stays FM's validator; DdM explanations subsume
  pure Farkas certs (equality lineage + bound facts).
- Remaining (future): soundness theorem for `checkExplanation`, Lean-term
  denotes link, `lynth_farkas` activation.

## Q6 — Finite-domain parent procedure + SAT-based finite solver
## (HIGHEST PRIORITY — first unfinished item)

Problem class: constraint puzzles over finite domains whose answer is
a subtype: Sudoku (+ variants), Star Battle, Towers/skyscrapers, and
generally `{ x // P x }` / `∃ x, P x` over finite types.
Example: `def sol : { g : SudokuGrid // Valid g ∧ extends g clues }
:= by lynth` with `SudokuGrid := Fin 9 → Fin 9 → Fin 9`.
Why we fail, in three layers: (1) `Witness` cannot even *form*
candidates for function-typed domains (no enumeration procedure for
them) and caps blind guessing at hundreds of scalars; (2) the search
space is 9^81 ≈ 2×10^77 — enumeration without propagation/backtracking
cannot touch it at any bound; (3) `decide` needs exhaustive kernel
evaluation (tiny analogues like `Fin 2 → Fin 2` already pass — only
scale is missing). Z3 maps this whole class to SAT.
- **Detector** (`Lynth/FinSearch/Detect.lean`): recognize synthesis
  goals over finite domains — `Fin n` (literal `n`), `Bool`, bounded
  `Nat` (`{ n // n < k }` via the existing `Witness` bound analysis),
  products/tuples thereof, and *functions* over these
  (`Fin n → Fin m`, nested). Compute a cardinality estimate (product
  of domain sizes); unknown/infinite → yield gracefully.
- **Router** (the parent procedure): if the estimate fits cheap
  enumeration, delegate to the existing `Witness` machinery; otherwise
  translate to the SAT child. Threshold as a named constant, with a
  test landing on each side.
- **SAT child** (`Lynth/FinSearch/Solve.lean`): encode decidable
  constraints to CNF — one-hot booleans per finite variable, problem
  constraints (`AllDifferent` → pairwise mutex + at-least-one, clues →
  units, more shapes per puzzle) — solve with `Cdcl.cdclSolve`
  (fuel-bounded; models + traces free), decode model booleans to a
  closed value term, verify by kernel-checked `decide`/`rfl` (fail
  loudly if the side is not closed-decidable). Soundness split:
  search untrusted, verdict proved.
- **Pilot ladder** (each an end-to-end test): 4×4 mini-Sudoku, then 9×9
  Sudoku, then Star Battle (regions + row/col counts + no-touching rule
  — tests expressiveness beyond `AllDifferent`), Towers/skyscrapers as
  stretch (visibility needs counting/comparison encoding).
- Tests `Test/FinSearch.lean` (pilots + `#print axioms` native-only +
  model-decode checks: decoded models always satisfy the encoded
  constraints); full suite green, commit.
- Note: absorbs the old Sudoku-pilot item (same project, smaller scope).

## Q7 — DRAT emission for the SAT core

- Emit standard DRAT (clause IDs + deletion) alongside internal
  `ResTrace`s; validate emitted proofs with the internal checker on fuzz.
- Done when: fuzz emits + validates, committed.

## Q8 — Watched literals for CDCL propagation

- Perf-only; semantics must not change: full fuzz agreement before/after
  (`Test/CdclFuzz.lean` must stay 0 mismatches), committed.

## Q9 — Cross-theory feedback (combination gap)

Problem class Z3 solves, we don't: goals needing facts to flow
*backward* through the pipeline. Example shape: arithmetic hyps pin
down `x = y`, but a congruence step over `f` needed that equality
*before* `arith` ran (`euf` already passed and never sees it).
Why we fail: fixed single-order pass; Z3 iterates theory solvers to a
fixpoint (CDCL(T)). Our constraint: SPEC forbids staged SMT loops, so
this must terminate by construction, not by fixpoint detection.
- Design bounded feedback: at most one second dispatch pass and/or
  forward sharing from `arith` (proven equalities in the style of
  EUF `shareDerived`), with an explicit SPEC-compliance argument
  (termination by construction, no theory staging).
- Start test-driven: write 2–3 concrete failing goals first, make them
  pass. Full suite green, commit.

## Q10 — Chained quantifier instantiation

Problem class: instances that enable further instances. Example shape:
transitive chains (`R x y`, `R y z`, `∀ a b c, R a b → R b c → R a c`
needing two rounds), congruence towers.
Why we fail: single pass over the entry context; Z3 saturates
E-matching inside its loop, so derived instances become new triggers.
- Bounded multi-round `instantiate` (round N matches against round
  N−1's instances too; cap rounds ≤ 3, total instances small,
  dup-suppressed; terminates by construction).
- Tests incl. a transitive-closure chain; full suite green, commit.

## Q11 — BV operator coverage

Problem class: shifts (`≪`, `≫`), comparisons (`ult`, `ule`, `slt`),
concat/extract, multiply/divide. Example: `(x ≪ 2) = x * 4`.
Why missing: our blast covers only and/or/xor/not/add/eq; Z3 blasts
the full operator set (plus simplifications).
- Add: shifts (barrel shifter or repeated concat), comparisons
  (subtractor + borrow/sign check), concat/extract (rewiring, gateless),
  mul (array multiplier, capped widths).
- Extend the bidirectional differential fuzz + e2e `Test/BV.lean`
  goals; full suite green, commit.

## Q12 — Arrays: nested stores + extensionality

Problem class: `select` over `store (store …)`, array equalities,
`select a i ≠ select b i → a ≠ b`.
Why missing: R1/R2 fire only on direct select-over-store; no fixpoint,
no extensionality rule; Z3's array solver saturates both.
- Iterate R1/R2 to a bounded fixpoint for nested stores.
- Contrapositive extensionality edge (Ne over equal-index selects
  yields array disequality) through the existing `Ne`-close path.
- Tests + full suite green, commit.

## Q13 — Datatype selectors and testers

Problem class: `head`/`tail`/`get?`/`isSome` goals, e.g.
`(h : l ≠ []) : l.head?.isSome = true`.
Why missing: only injectivity/discrimination implemented; Z3's
datatype solver also eliminates selectors and splits testers.
- Selector rules (`head (cons a as) = a`, `Option.getD (some a) d = a`,
  …) with core-lemma proofs found empirically (as `Arrays` did with
  `getElem_set_self`); tester splitting via the `Ne`-close path.
- Wire as EUF sub-procedure; `Test/Datatypes.lean` additions; full
  suite green, commit.

## Q14 — Scheduled regression watch (recurring tick)

- `lake build` + every `Test/*.lean` suite; report failures only.
- One-liner: `run the Q14 regression watch in /root/lynth`.
