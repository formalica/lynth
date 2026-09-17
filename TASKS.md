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
6. Commit when green (`git add -A`, short message); report what was
   done, test results, and what remains open. Then stop — one task
   per tick. The next tick repeats from step 1, so the backlog drains
   automatically.

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

## Q5 — Farkas extraction from Simplex + `lynth_farkas` activation

- Track row lineage (combos over original constraints) through
  `Simplex.pivot`; at UNSAT combine row lineage with bound facts into a
  `FarkasTrace`; validate via `FarkasSound.checkCert`.
- Remaining hard part (separate task if needed): Lean-term denotes link
  (term algebra over goal terms) to close goals directly by certificate.
- Tests: extraction agrees with FM certs on fuzz; committed.

## Q6 — DRAT emission for the SAT core

- Emit standard DRAT (clause IDs + deletion) alongside internal
  `ResTrace`s; validate emitted proofs with the internal checker on fuzz.
- Done when: fuzz emits + validates, committed.

## Q7 — Watched literals for CDCL propagation

- Perf-only; semantics must not change: full fuzz agreement before/after
  (`Test/CdclFuzz.lean` must stay 0 mismatches), committed.

## Q8 — Scheduled regression watch (recurring tick)

- `lake build` + every `Test/*.lean` suite; report failures only.
- One-liner: `run the Q8 regression watch in /root/lynth`.
