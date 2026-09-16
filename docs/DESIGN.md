# lynth architecture

`lynth` is a proof-producing solver front-end in the style of Z3, operating directly
on Lean/Mathlib goals.

## Goals

- `theorem thm : a + b = b + a := by lynth` — propositional goals.
- `def f : {n : Nat // pred n} := by lynth` — computational goals; lynth must
  instantiate the witness and produce a computable value.

## Core concepts

### Procedures
A **procedure** is a specialized solver with its own internal representation
and translation to/from Lean terms (like a Z3 theory solver with its own
internal language). There is no separate "theory hierarchy"; procedures own
their internal theories, and a procedure may invoke sub-procedures.

Every procedure:
- receives the problem in a canonicalized form,
- runs a **decision procedure**,
- on success, returns a **reconstructed proof** (proof-producing; the caller
  re-checks everything through the kernel),
- on failure, returns a **procedure explanation**.

### Explanations (Z3-style, but lifted to Lean)
Z3 theory solvers return conflict explanations over shared variables, and
T-lemmas are shared through the base SAT language. Lean is much more
expressive, so we keep **everything in Lean terms**: an explanation is a list
of new facts, each with a kernel-checked proof term:

```
ProcedureExplanation := list of (Prop, proof)
```

A failed procedure returns new information as `var_name = x` style predicates
(e.g. a normalization lemma `c.val = 3` or `t = t'`) plus the proof. The next
procedure consumes these facts directly. This replaces Z3's variable-sharing
mechanism by explicit, generically typed, provably-valid facts.

### Correctness through reconstruction theorems
Decision procedures compute certificates (untrusted). A **reconstruction
theorem** proves the certified answer is sound; the final proof of the user's
goal is built by applying the reconstruction theorem to the computed
certificate. The statements live in `Lynth/Axioms.lean` as sound,
checker-conditioned theorems (`ResTrace`/`FarkasTrace` with stub checkers);
as real checkers land the same statements become load-bearing. There are
no `sorry`s and no internal axioms anywhere: CI enforces that user-facing
tests depend only on Lean's native axioms.

## Pipeline

```
goal
 └─ Frontend.dispatch: procedures in order (witness → euf → ring → sat → arith)
     ├─ each failure returns an explanation + may assert proven facts
     │  (e.g. EUF shares derived equalities) for later procedures
     └─ final error lists every procedure's outcome
 └─ Procedures (each with internal representation + explanation)
     ├─ Witness: Subtype/Exists over Nat/Int/Bool/Prod/Fin (computable)
     ├─ EUF: equality graph, congruence, Ne/False, sharing (zero axioms)
     ├─ Ring: semiring normalizer
     ├─ Sat: CDCL (learning, VSIDS, restarts, traces) over Tseitin skeleton
     └─ Arith: FM + Simplex + branch-and-bound over exact Int/Nat translation
 └─ Reconstruction: certificates (Farkas lineage, resolution traces) are
    validated by independent checkers; final proofs are kernel-checked
    tactics guided by oracle verdicts (`omega`, `grind`, `ring`, …)
```

## Roadmap status

Done: procedure plumbing, CDCL core, Tseitin oracle, EUF, FM, Simplex,
branch-and-bound, witnesses, ring, reconstruction-theorem statements,
16 green suites with native-axioms-only discipline.
Next: watched literals, DRAT emission, Farkas-from-Simplex extraction,
activating `lynth_sat_resolve` / `lynth_farkas` end-to-end
(see `docs/PROCEDURES.md` and `docs/Z3-NOTES.md`). Combination stays
sequential (no SMT loop, per SPEC).

## Testing discipline

Every user-facing test file is checked with `#print axioms` and must depend
only on Lean's native axioms (`propext`, `Classical.choice`, `Quot.sound`).
CI enforces this. There are no `sorry`s and no `axiom`s in the codebase.
