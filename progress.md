# lynth progress

Living status snapshot. Update on each tick: move finished items to
"Done", keep "Next" pointing at the lowest unfinished `TASKS.md` item.
Direction lives in `SPEC.md`; backlog lives in `TASKS.md`.

## HEAD

- Commit `1879090` — TASKS.md loop driver protocol.
- Tree status: `SPEC.md` has uncommitted reformatting (not yet reviewed);
  otherwise clean.

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
- `Ring` (`ring`), `Nlin` (`nlinarith`) kernel-checked normalizers.
- `Sat`: CDCL (first-UIP learning + resolution traces + checker,
  VSIDS, geometric restarts), Tseitin oracle over goal + hypotheses,
  DPLL reference; fuzz-validated (CDCL vs DPLL, Tseitin vs truth tables).
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

- `TASKS.md#Q6` — DRAT emission for the SAT core
  (fuzz emits + validates).
- Then Q7 watched literals; Q8 is the recurring regression watch.

## Open gaps / risks (honest list)

- Lean-term denotes link for certificates (translation trusted +
  fuzz-tested; kernel re-check is the safety net).
- Full MBQI blocked (open-term evaluation over infinite domains);
  only decidable finite fragments are in reach.
- No CDCL(T)/Nelson-Oppen loop by design (SPEC: sequential
  explanation-passing instead).
- `SPEC.md` working-tree reformatting uncommitted — review before
  committing.
