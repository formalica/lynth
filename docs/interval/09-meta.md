# 09 — Meta goals (Phase 7): synthesized approximation functions

## 1. Goal shapes (`Goals/Meta.lean`)

```
{ f : ℚ → ℚ // ∀ x : ℚ, |E(↑x) - ↑(f x)| < tol }
{ f : ℚ → ℚ // ∀ x : ℚ, a < x → x < b → |E(↑x) - ↑(f x)| < tol }
{ f : ℚ → ℚ → ℚ // ∀ a b : ℚ, if C a b then |E(a,b) - ↑(f a b)| < tol else f a b = 0 }
{ f : ℕ → ℚ // ∀ n : ℕ, |E(n) - ↑(f n)| < tol }         -- e.g. partial sums
complex outputs: { f : ℚ → ℚ × ℚ // ∀ x, ‖E(x) - (↑(f x).1 + ↑(f x).2 * I)‖ < tol }
```

`E` is reified with the inputs as variables (`var .real i` for ℚ inputs cast to
ℝ, `var .nat i` for ℕ inputs).  The domain `D : Box` (list of extended
intervals) comes from the hypotheses (`a < x → x < b`) or is `⊤`.

## 2. Adaptive strategy (default)

Runtime function (generic library code, **computable**, never reduced by the
kernel, so well-founded recursion / `Nat.find` are fine):

```lean
/-- the enclosure at precision level `k` for the input point(s) `xs` -/
def Meta.encl (e : Expr .real) (k : Nat) (xs : List ℚ) : Ival :=
  e.eval (Ctx.make (precOf k)) ⟨[], xs.map (Ival.ofRat (precOf k)), []⟩
def Meta.good (e) (tolLo : Dy) (xs) (k : Nat) : Bool :=
  match (encl e k xs).width? with | some w => w < 2·tolLo | none => false
/-- approximation: midpoint of the first good enclosure -/
def Meta.approx (e : Expr .real) (tolLo : Dy) (xs : List ℚ)
    (h : ∃ k, Meta.good e tolLo xs k = true) : ℚ :=
  (encl e (Nat.find h) xs).midRat
```

`precOf k := 32 * (k + 1)` (or doubling), so the search is short.
The synthesized witness is
`fun x => Meta.approx eTerm tolLo [x] (Meta.conv_exists … x hx)`
where `eTerm` is the reified `Expr` **term** (a closed, computable constant
built from registry records).  Only `h` (a proof, erased at runtime) depends on
the convergence theory below.

Correctness theorem (generic):

```lean
theorem Meta.approx_spec (h) : |e.denote ⟨[], xs.map (↑), []⟩ - Meta.approx e tolLo xs h| < tolLo.toReal
  -- from eval_sound at level `Nat.find h`, `Nat.find_spec`, midpoint lemma
```

and `tolLo ≤ tol` is a closed check.

### 2.1 Convergence theory (`Cert/Conv.lean`)

```lean
/-- interval extension `ev : Ctx → Ival → Ival` converges at `x` -/
def ConvAt (ev : Nat → Ival → Ival) (x : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∃ k₀, ∀ k ≥ k₀, ∀ X : Ival, X.isFinite → x ∈ X → X.widthR < δ →
    (ev k X).isFinite ∧ (ev k X).widthR < ε
```

(`widthR` = real width; `ev k := f.ev (Ctx.make (precOf k))`.)  For binary
functions the analogous definition with two input intervals.

Per-function capability (in `Fn1`, 03 §3):

```lean
  conv    : Ctx → a.Enc → Bool          -- "every point of X is a convergence point"
  conv_ok : ∀ c X x, conv c X = true → a.Mem X x → ConvAt (fun k => ev (Ctx.make (precOf k))) x
```

(the `Ctx` argument of `conv` is only used to access π etc. for domain tests
such as `X ⊆ (-π/2, π/2)`; soundness quantifies over all `x ∈ X`.)

Generic structural check and theorem:

```lean
/-- over the domain box D: every node's argument range (plain interval eval
    over D at a fixed precision) lies in that node's convergence domain -/
def Expr.convCheck (c : Ctx) : Expr t → IEnv → Bool
theorem Expr.convAt_of_convCheck (h : e.convCheck c D = true) (hx : xs ∈ D) :
    ConvAtE e xs     -- ∀ ε>0, ∃ k₀, ∀ k ≥ k₀, width(encl e k xs) < ε
theorem Meta.conv_exists (h : e.convCheck c D = true) (hx : xs ∈ D) (htol : 0 < tolLo) :
    ∃ k, Meta.good e tolLo xs k = true
```

Proof of `convAt_of_convCheck`: induction on `e`, composing the `ConvAt`
statements: for `c1 f a`, the argument enclosures converge to width 0 and
contain `a.denote`, so eventually their width `< δ_f` — then `f`'s `ConvAt`
applies.  Literals/variables: `Ival.ofRat (precOf k) q` has width
`≤ 2^{-(precOf k)}·|q|` → 0.  `sum` with point `n`: finite induction.
`integral`: uniform version via compactness (see §2.3).

### 2.2 Per-function convergence obligations

For a monotone function computed by endpoint point-kernels
`[lo_k(X.lo), hi_k(X.hi)]`:

```lean
theorem convAt_of_monotone_kernels (hF : ContinuousAt F x)
    (hlo : ∀ a, lo_k a ≤ F a) (hhi : ∀ a, F a ≤ hi_k a)
    (herr : ∀ B, ∃ K, ∀ k ≥ K, ∀ a, |a| ≤ B → hi_k a - lo_k a ≤ 2^{-k})   -- kernel accuracy
    : ConvAt ev x
```

So each monotone function needs (i) continuity (Mathlib), (ii) a *kernel
accuracy lemma*: the gap between the upper and lower point kernel is
`≤ C(B)·2^{-precOf k}` on bounded arguments.  For the Taylor-based kernels
this follows from: Horner rounding error `≤ (#terms)·2^{-w}·scale` plus the
remainder `≤ 2^{-w}` by the choice of `N`, both proven once in
`Series/Horner.lean` (`hornerI_width_le`) — write the kernels so that the
width bound is easy (fixed-point style: all partial results rounded to the
same absolute exponent `-w` after argument reduction).

Required for the tests: arithmetic (`add sub mul neg inv` (away from 0) `npow`),
`natCast`, `exp`, `log` (on `(0,∞)`), `cos`, `sin`, `sum` node,
`integral` node (for `integralExpNegSqMeta`).

### 2.3 Integral node convergence

`Quad.eval` at level `k` uses the uniform partition into `2^{k/4}` pieces with
degree-0 models (Riemann enclosure `Σ wᵢ·eval(body, pieceᵢ)`).  Width →
0 because the body's `ConvAt` holds at every point of the compact `[a,b]`
(uniformity by compactness: `IsCompact.elim_finite_subcover` / Lebesgue
number lemma `lebesgue_number_lemma_of_metric`).  This is only needed for meta
goals; the quadrature used for closed goals (07) is independent.

## 3. Piecewise-polynomial strategy (bounded, tame domains)

When `D` is a bounded box and the TM of `E` over `D` has moderate derivatives
(heuristic: TM remainder at degree 12 over ≤ 256 pieces below `tol/4`):
* natively compute a partition `D = ∪ Pᵢ` and polynomials `pᵢ` (dyadic
  coefficients, Chebyshev interpolation or truncated TM polynomials);
* witness: `fun x => evalPiecewise table x` (computable, rational Horner);
* proof: for each piece `∀ x ∈ Pᵢ, |E(x) - pᵢ(x)| < tol` by the B&B/TM checker
  (06, 07) on the expression `E(x) - pᵢ(x)` (the polynomial is reified as an
  `Expr` built from literals), combined by a generic `piecewise_spec` lemma
  (the lookup `evalPiecewise` selects the piece containing `x`).
Decision rule (`Goals/Meta.lean`): try piecewise if `D` bounded and the
native estimate says ≤ 256 pieces; otherwise adaptive.  Both produce valid
answers; piecewise yields O(1) evaluation.

## 4. Conditional shape (`integralExpNegSqMeta`)

`if a < b ∧ IntegrableOn g (Icc a b) then |∫ … - f a b| < tol else f a b = 0`:
witness `fun a b => if a < b then Meta.approx … else 0`; proof by
`by_cases`/`split_ifs`: in the `a < b` branch the integrability conjunct is
provable (continuity of the integrand: `Expr.measurable` + boundedness, 07 §2);
if `a < b` but the (classical) condition is false we derive a contradiction
from the integrability proof; if `¬ a < b` both branches produce `0`.
(Requires the test fix `open Classical`, see 12.)

## 5. Milestone

* **M12** convergence capabilities (arith, exp, log, sin, cos, natCast, sum)
  + `Goals/Meta.lean` adaptive: `expMeta`, `expExpMetaRange`, `logExpMeta`,
  `sumExpCosMeta`.
* **M13** integral convergence + conditional shape: `integralExpNegSqMeta`;
  piecewise-polynomial strategy (bounded domains).
