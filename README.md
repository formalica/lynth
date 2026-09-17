# lynth — a proof-producing solver tactic for Lean 4

`lynth` fills in proofs *and* computable data from the types you write:

```lean
import Lynth

theorem thm (a b : Nat) : a + b = b + a := by lynth

def f : { n : Nat // 0 < n } := by lynth  -- f = ⟨1, ⋯⟩, computable
#eval (f : Nat)  -- 1

theorem ex : ∃ n : Int, n < 0 := by lynth  -- −1

def pp : { p : Nat × Nat // p.1 + p.2 = 3 } := by lynth  -- (0, 3)
```

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
