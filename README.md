# lynth — a proof-producing solver tactic for Lean 4

`lynth` fills in proofs *and* computable data from the types you write:

```lean
module

import Lynth

theorem thm (a b : Nat) : a + b = b + a := by lynth

def f : { n : Nat // 0 < n } := by lynth  -- f = ⟨1, ⋯⟩, computable
#eval (f : Nat)  -- 1

theorem ex : ∃ n : Int, n < 0 := by lynth  -- −1

def pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth  -- (0, 3)
```

## Public API

Use `import Lynth` and describe the goal to `lynth`. The main entry points are
the tactic, its checking/search options, and the provided mathematical functions:
`Real.erf`, `Real.Si`, `Real.dirichletEta`, `Real.airyAi`, their complex counterparts,
`Real.digamma`, `Real.zeta`, `Complex.arcsin`, `Complex.artanh`,
`Complex.HGFun`, `Complex.besselI`, `Complex.ellipticK`, and `Complex.ellipticE`.

For example, `set_option lynth.interval.trust "kernel"` selects kernel checking;
`"native"` selects native checking and `"auto"` uses the existing cost budget.
`lynth.interval.kernelBudget`, `lynth.interval.maxPrec`, and
`lynth.interval.complexIntegralSteps` retain their existing meanings and defaults.

The import also exports the declarations referenced by generated proofs and the
types and computational definitions needed to check them. Users do not need to
call these declarations. Lemmas used only inside theorem proofs remain private.

Implementation modules use Lean's `module` system. Selected internal helpers and
lemmas exercised by regression tests are public; other procedures remain private.
Use a `module` header in consumer files to benefit from the smaller import interface.
Internal unit tests also use `import Lynth`; the helpers they exercise are public.
Six internal tests retain their original file headers to preserve their existing heartbeat limits.
The separate `lynth_grind` API is an exception and remains available through
`import Lynth.Grind.Tactic`.

## Architecture (Z3-style procedures, Lean-native)

Like Z3, `lynth` is a pipeline of specialized **procedures**, each with its
own internal language and translation to/from Lean terms. Unlike Z3 there is
no separate theory hierarchy and no staged SMT loop: every procedure either
closes the goal with a kernel-checked proof or returns an **explanation**
(new proven facts, e.g. `x = v` equalities) that later procedures consume.
Variable sharing *is* explanation sharing.

| Procedure | Fragment | Method |
|---|---|---|
| `Witness` | `{x // P x}`, `∃ x, P x` over `Nat`/`Int`/`Bool` | bounded enumeration + kernel-checked side conditions |
| `EUF` | equalities, congruence, disequalities | graph closure, `congr` chains, contradiction of `≠` hyps; shares derived equalities |
| `Ring` | semiring identities | `ring` normalizer (cf. Z3's Gröbner core) |
| `Sat` | propositional skeleton of goal + hypotheses | CDCL: first-UIP learning with resolution traces, VSIDS, geometric restarts, Tseitin encoding |
| `Arith` | linear `Int`/`Nat` | Fourier–Motzkin with Farkas lineage + validation, tableau Simplex (Dutertre–de Moura), branch-and-bound; exact integer translation |

Reconstruction theorems live in `Lynth/Certificates.lean` as sound,
checker-conditioned statements. There are no `sorry`s and no `axiom`s:
every test is `#print axioms`-checked to depend only on Lean's native
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Layout

- `Lynth/` — procedures (`Sat/`, `Euf/`, `Arith/`, `Ring/`, `Witness.lean`),
  dispatcher (`Frontend.lean`), entry point (`Basic.lean`: `by lynth`).
- `Test/` — 16 suites run via `lake env lean Test/<Name>.lean`
  (also enforced by CI).
- `docs/` — `DESIGN.md` (architecture), `PROCEDURES.md` (registry),
  `Z3-NOTES.md` (pinned Z3 survey + mapping).

## Pinned Z3 reference

Implementation survey of Z3 at `d5d92669ebccc2bb00cecfa72f0f2787941ba3ce`
(see `docs/Z3-NOTES.md`): `src/sat` (CDCL + DRAT), `src/math/simplex` +
`src/math/lp` (Simplex), `src/smt` (theory combination).

## Upstream commits

- Lean 4 (`Grind`): `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`
- CreuSAT: `232edff08ec6a5713cc3d61797f353550ca94d6f`
