# Z3 implementation notes (pinned)

Pinned Z3 commit: `d5d92669ebccc2bb00cecfa72f0f2787941ba3ce`
(cloned to `/tmp/opencode/z3`; `git rev-parse HEAD`).

## SAT core — `src/sat/`

Entry: `src/sat/sat_solver.cpp` — `solver::propagate_core` (unit
propagation, line ~989), `solver::resolve_conflict` /
`resolve_conflict_core` (conflict analysis, lines ~2464–2521),
`resolve_conflict_for_unsat_core` (line ~2761). Supporting machinery:

- watched literals + binary/non-learned clause paths (line ~2265),
- DRAT proof logging: `src/sat/sat_drat.h`, `sat_drat.cpp`,
- equation elimination: `sat_elim_eqs.cpp`, AIG finding, ANF simplifier,
  asymmetric branching (`sat_asymm_branch.cpp`), big-clause handling.

So Z3 SAT = CDCL with first-UIP learning, VSIDS-style heuristics,
restarts, preprocessing/inprocessing, and proof emission.

## Arithmetic — `src/math/`, `src/smt/`

- `src/math/simplex/simplex.h` — `class simplex` (legacy tableau Simplex).
- `src/math/lp/` — modern LP solver (`lp_settings.h`:
  `simplex_strategy_enum`), used by the arithmetic theory solver.
- `src/smt/` — theory integration: `arith_eq_solver.*`,
  `arith_eq_adapter.*`, `smt_arith_value.*`, `diff_logic.h`,
  plus `dyn_ack`, `mam`, `qi_queue` (E-matching/MBQI for quantifiers).

So Z3 LRA = Simplex over rationals; integers via branch-and-bound and
cuts on top; equalities shared through congruence-closure adapters.

## What lynth borrows (incrementally)

| Z3 piece | lynth status |
|---|---|
| CDCL core (`sat_solver.cpp`) | CDCL with first-UIP learning + backjump + VSIDS + geometric restarts (`Lynth/Sat/Cdcl.lean`); DPLL reference (`Solver.lean`); watched literals TODO |
| DRAT proofs (`sat_drat.*`) | resolution traces recorded per learnt clause + independent checker (`Cdcl.checkTrace`), fuzz-validated; full DRAT emission TODO |
| Simplex/LP (`math/simplex`, `math/lp`) | FM elimination with Farkas lineage (`Lynth/Arith/Fourier.lean`); tableau Simplex à la Dutertre–de Moura with models (`Lynth/Arith/Simplex.lean`), differential-tested vs FM |
| Theory combination (`smt/*`, eq adapters) | Explanation facts with proofs (`Lynth/Procedure.lean`); no Nelson-Oppen, sharing is explicit equality facts |
| Untrusted oracle + proof | Oracle-guided kernel-checked tactics today; `lynth_sat_resolve` / `lynth_farkas` axioms track future certificate soundness |

## Incremental plan

1. CNF translation from Lean `Prop` skeletons (Tseitin) into `Lynth.Sat.Syntax.CNF`.
   DONE for goal + hypotheses (`Encode.lean`, `Abstract.lean`).
   NOTE: collectors must skip non-`default` local decls — Lean parks the
   declaration itself (`_example`, `auxDecl`) in context, and using it
   "proves" goals from themselves (caught + fixed).
2. Learned clauses + resolution-trace checker → discharge `lynth_sat_resolve`.
3. Simplex tableau over `Rat` in `Lynth.Arith`, Farkas extraction → discharge `lynth_farkas`.
4. Congruence-closure (EUF) procedure for `var = value` fact propagation.
5. Combination stays sequential explanation-passing (SPEC: no iterative
or staged SMT solving); EUF sharing is the mechanism, extended per procedure.
