# 10 — Complex numbers in every phase

Complex support is a first-class requirement.  The AST is typed (`Ty.cplx`),
so every generic component (evaluator, soundness, reifier, sums, integrals,
meta, certificates) works for complex values once the complex functions are
registered.  Enclosures are rectangles `CBox` (02 §4).

## 1. Reification of complex terms

* Types: a term of type `ℂ` is reified at `Ty.cplx`; `ℝ → ℂ` coercion
  `Complex.ofReal x` / `(x : ℂ)` → `c1 ofRealFn`; numerals in ℂ via the exact
  evaluator (`norm_num` works in `ℂ` for rational numerals) → `c1 ofRealFn (lit q)`.
* `Complex.I` → `c0 iFn` (ev = `⟨pt 0, pt 1⟩`).
* Real-valued views: `Complex.re z`, `Complex.im z`, `‖z‖` (`norm`),
  `Complex.abs z` (if present), `Complex.normSq z`, `Complex.arg z` —
  `Fn1 .cplx .real` records.
* Complex binary ops `+ - * / ^ℕ`, `Complex.exp`, `Complex.log`,
  `Complex.sin/cos/sinh/cosh/tan`, `z ^ (w : ℂ)` (`Complex.cpow`),
  `starRingEnd ℂ z` (conj).

## 2. Complex function kernels (`Fns/Complex.lean`)

With `z = a + bi` and enclosure `⟨A, B⟩`:

| function | enclosure (real interval ops) | Mathlib facts |
|---|---|---|
| exp | `re = exp A · cos B`, `im = exp A · sin B` | `Complex.exp_re`, `Complex.exp_im` |
| sin | `re = sin A · cosh B`, `im = cos A · sinh B` | `Complex.sin_re`, `Complex.sin_im` |
| cos | `re = cos A · cosh B`, `im = -(sin A · sinh B)` | `Complex.cos_re`, `Complex.cos_im` |
| sinh, cosh | via exp or the analogous formulas | `Complex.sinh_re`, … |
| norm | `√(A² + B²)` (dependency-aware squares) | `Complex.norm_def`, `Complex.normSq_apply` |
| arg | if `A.lo > 0`: `arctan(B/A)`; if `B.lo > 0`: `π/2 - arctan(A/B)`; if `B.hi < 0`: `-π/2 - arctan(A/B)`; else (box meets the non-positive real axis) → `[-π, π]` | `Complex.arg_of_re_pos` (`arg z = arcsin (z.im / ‖z‖)`), `Complex.arg_of_im_pos`, `Complex.arg_of_im_neg`, `Complex.arg_le_pi`, `Complex.neg_pi_lt_arg` |
| log | `re = log ‖z‖` (needs `0 ∉ box`), `im = arg z` | `Complex.log_re`, `Complex.log_im` |
| cpow `z^w` | `z = 0` excluded: `exp (w · log z)` | `Complex.cpow_def_of_ne_zero` |
| sqrt (as `z ^ (1/2 : ℂ)`) | via cpow; optional direct formula | |
| inv, div | `CBox.inv`, `CBox.div` | `Complex.inv_re`, `Complex.inv_im` |
| conj | `⟨A, -B⟩` | `Complex.conj_re`, `Complex.conj_im` |

Branch cut rule: any function whose Mathlib definition has a branch cut
(`log`, `arg`, `cpow`) returns ⊤ in the imaginary part (or the whole box) when
the argument box meets the cut; this is always sound.

## 3. Goal shapes with complex data (`Goals/Approx.lean`, `Goals/Closed.lean`)

* `{p : ℚ × ℚ // ‖E - (↑p.1 + ↑p.2 * Complex.I)‖ < tol}` — witness `p` from the
  midpoint of the box of `E`; proof by the closed checker (the atom
  `‖E - (↑p.1 + ↑p.2 * I)‖ < tol` reifies with complex subtraction and `norm`).
* `{p : ℚ × ℚ // |E.re - ↑p.1| < tol ∧ |E.im - ↑p.2| < tol}` (componentwise).
* Real-valued goals containing `.re`, `.im`, `‖·‖` of complex expressions
  (e.g. `(riemannZeta s).re`, once zeta exists) — nothing special.
* Closed inequalities between norms of complex expressions.

## 4. Complex Taylor models and integrals

`CTM := (re : TM, im : TM)` over a real variable piece; complex functions of
a complex TM use the complex versions of `TayCap` (`expand` returns complex
dyadic coefficients as pairs and a `CBox` error), with soundness from the
complex Taylor bound (`Complex.exp_bound` for exp; for general holomorphic `F`
use Cauchy estimates — defer, implement exp/sin/cos first).  Integral of a
`ℂ`-valued integrand over a real interval:
`∫ f = ∫ re f + I · ∫ im f` (`intervalIntegral.integral_re`/`im` or
`integral_ofReal` + `Complex.ext`), so complex quadrature reuses real
quadrature on both components.

## 5. Complex sums and series

* Finite sums: the `sum` node is generic (`Ty.addE .cplx = CBox.add`).
* Series `f : ℕ → ℂ`: summability via norms (`Summable.of_norm`,
  `summable_norm_iff` fails in general → use `Summable.of_norm_bounded` with
  the AIA of `‖f k‖`); `tsum ∈ partial + closed disc of radius T` → box
  `partial ± T` in both components.

## 6. Complex meta goals

`{f : ℚ → ℚ × ℚ // ∀ x, ‖E(x) - (↑(f x).1 + ↑(f x).2 * I)‖ < tol}`:
`Meta.approx` over `CBox` (width = max of component widths; the norm error of
a midpoint is `≤ √2 · max width / 2`, so use `tol/√2` → dyadic `tolLo`).
Convergence capabilities for complex exp/sin/cos/norm follow from their
formulas in terms of real functions (composition of real `ConvAt`).

## 7. New tests (added by this project)

`Test/IntervalArith/Complex.lean` (see `12-tests.md` §4):
exp at a complex point, `(exp (I·π/3)).re = 1/2`, complex log/arg, `‖·‖` of a
complex sum, integral of `exp(I·t)` over `[0, 1]`, a complex meta goal.

## 8. Milestone

* **M4c** (with M4): complex arithmetic + exp/sin/cos/norm/re/im/arg/log +
  complex witness shapes.
* **M10c** complex quadrature; **M11c** complex series; **M12c** complex meta.
