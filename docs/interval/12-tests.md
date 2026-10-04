# 12 — Tests: inventory, routes, fixes

Run a suite: `lake env lean Test/IntervalArith/<File>.lean`.
Axiom pins: kernel mode keeps `[propext, Classical.choice, Quot.sound]`;
a test closed in native mode lists its auxiliary `…native_decide.ax_…` axiom.

## 1. Statement fixes (approved by the user)

| file | fix |
|---|---|
| `ApproxRoots.lean` | `RootOrNoRoot f 1 3/2 tol` → `RootOrNoRoot f 1 (3/2) tol`; same for `1/2`, `1/10`, `4/5` arguments |
| `ImproperIntegrals.lean` IC09 | `ℝ ^ 10` → `Fin 10 → ℝ` (and `Set.Icc (0 : Fin 10 → ℝ) 1`) |
| `LinearAlgebra.lean` | `!![![2,1,1], ![1,3,-1], ![1,-1,2]]` → `!![2, 1, 1; 1, 3, -1; 1, -1, 2]`; `!![![0,-1],![1,0]]` → `!![0, -1; 1, 0]` |
| `Meta.lean` | add `open Classical in` before `integralExpNegSqMeta` (undecidable `if`) |
| `Taylor.lean` | `Function.iterate deriv k f z` → `deriv^[k] f z` |
| `Compositions.lean` MP31 | `regularizedGaussHGFun 1 2 3 (-5)` → a convergent point `(-1/2)` (Mathlib defines the function as the power-series sum, which diverges for `|z| ≥ 1`; its Mathlib value at `-5` is `0`) — update the docstring value |

## 2. Inventory and routes

Legend: milestone (see 13), **D** = deferred (special functions, deriv,
Taylor coefficients, ODE, linear algebra, improper/divergent integrals,
logical extrema), **L** = logical/symbolic (other procedures may solve).

### Basic.lean (T01–T06) — M4
cos/sin of rational multiples of π, exp, log(π/100), rpow, sqrt — Approx.

### Compositions.lean (MP01–MP35)
* M4: MP01, MP02, MP05, MP06, MP08–MP16, MP17, MP19 (Nat.bell exact), MP20,
  MP21 (bernoulli exact), MP22, MP24, MP25, MP28, MP29.
* Gamma (implemented, `Fns/Gamma.lean`, standard footprint):
  MP03, MP04, MP23.
* D: MP07 (zeta), MP18 (Euler γ — could be M5 via
  `eulerMascheroniSeq` bounds, tolerance π/100), MP26 (agm — M5 candidate via
  `agmSequences` bounds), MP27 (digamma), MP30–MP35 (hypergeometric).

### Special.lean
T20 (π) M4; B06 (root of x³-2) M6 (root finder, or closed check with a guessed
witness); T18 (Gamma — implemented, standard footprint), T19 (zeta) D.

### Discrete.lean — M5
MD01, MD03, MD04, MD06, MD07 interval (discrete witnesses via `Goals/Discrete.lean`);
MD05 exact ℕ (`decide`, zero axioms, closed by `witness`);
MD02 needs Gamma (done) **and** `Nat.floor` (now registered; closed with
standard footprint, needs `maxHeartbeats 1000000`).

### Sums.lean
T12, T13, T14 M5 (finite sums); B01, B03 M5 (closed props with 1000/100-term
sums vs π); T15 infinite product D; B02, P-style `∀ n` identities L.

### Theorems.lean
P21, P23, P24, P27, P29 M6; P22, P25, P26 M7; P28 (Gamma — implemented,
standard footprint); P30 L.

### Roots.lean — M6.  ApproxRoots.lean — M6 (after statement fix).

### Ranges.lean — M8 (T07–T11, MR01–MR03).

### Extrema.lean
E02–E05 M8; E01 (exact min, tol 0), E06–E11 (no extremum) L/D.

### Integrals.lean — M10 (T15–T17).
### ImproperIntegrals.lean
IC01, IC02, IC03, IC08 M10; IC04–IC07 (improper) D; IC09 (10-D) D;
ID01–ID10 (divergence) D.

### InfiniteSums.lean — M11 (all).

### Meta.lean — M12 (expMeta, expExpMetaRange, logExpMeta, sumExpCosMeta),
M13 (integralExpNegSqMeta).

### Differentiation.lean, Taylor.lean, LinearAlgebra.lean, Linear.lean
D (Linear B04/B05 may be solved by exact rational arithmetic later).

## 3. Internal tests (new files)

* `Test/Interval/Num.lean` — `Dy`/`Ival`/`CBox` `#eval` + `decide +kernel`
  smoke tests, rounding directions, FTIA spot checks.
* `Test/Interval/Fns.lean` — every registered function: `#eval` enclosure at a
  few points vs. known digits, one `lynth` goal each, kernel and native mode.
* `Test/Interval/Reify.lean` — reifier round-trips (`#check` proofs).

## 4. New complex tests (`Test/IntervalArith/Complex.lean`)

```lean
def cexp_one_two : { p : ℚ × ℚ // ‖Complex.exp (1 + 2 * Complex.I) - (↑p.1 + ↑p.2 * Complex.I)‖ < 1 / 1000000 } := by lynth
def cexp_re : { x : ℚ // |(Complex.exp (Complex.I * (Real.pi / 3))).re - ↑x| < 1 / 1000000 } := by lynth   -- 1/2
def clog_im : { x : ℚ // |(Complex.log (-1 + Complex.I)).im - ↑x| < 1 / 1000000 } := by lynth          -- 3π/4
def cnorm_sum : { x : ℚ // |‖∑ k ∈ Finset.range 10, (Complex.I / 2) ^ k‖ - ↑x| < 1 / 1000000 } := by lynth
def csin_parts : { p : ℚ × ℚ // |(Complex.sin (1 + Complex.I)).re - ↑p.1| < 1/100000 ∧ |(Complex.sin (1 + Complex.I)).im - ↑p.2| < 1/100000 } := by lynth
theorem cnorm_bound : ‖Complex.exp (Complex.I * 2) + 1‖ < 21 / 20 := by lynth    -- 2|cos 1| ≈ 1.0806? (check value before pinning)
def cint_exp_it : { p : ℚ × ℚ // ‖(∫ t in (0:ℝ)..1, Complex.exp (Complex.I * t)) - (↑p.1 + ↑p.2 * Complex.I)‖ < 1 / 10000 } := by lynth   -- M10c
def cmeta_exp_it : { f : ℚ → ℚ × ℚ // ∀ x : ℚ, -10 < x → x < 10 → ‖Complex.exp (Complex.I * x) - (↑(f x).1 + ↑(f x).2 * Complex.I)‖ < 1 / 1000 } := by lynth  -- M12c
```

(Values must be double-checked numerically before pinning; e.g.
`‖e^{2i} + 1‖ = 2|cos 1| ≈ 1.0806`, so the bound `21/20` is false — use
`< 11/10`.)
