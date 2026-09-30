# 06 — Box goals (Phase 4): branch & bound, AD, ranges, roots, extrema

## 1. Boxes and variables

A *box problem* has real variables `x₀ … x_{m-1}` (Lean fvars after `intro`)
with enclosures `B : List Ival` derived from hypotheses:
`x ∈ Set.Icc a b`, `a ≤ x`, `x ≤ b`, `a < x`, `x < b`, `x ∈ Set.Ioo a b`, …
(`a, b` closed real terms → outer dyadic bounds: `a.lo`, `b.hi`).  Rational
variables `y : ℚ` appearing as `((y:ℚ):ℝ)` are treated as real atoms whose
bounds come from `y ∈ Set.Icc (0:ℚ) 1` via `Rat.cast_le`.  Unbounded sides
become `none` (extended intervals).

Reification uses `RCtx.vars := [x₀, …]`, `SEnv := ⟨[], [x₀, …], []⟩`.

## 2. Branch & bound certificates (`Cert/BB.lean`)

```lean
inductive BBTree where
  | leaf                                   -- plain interval check of the property
  | mono (dim : Nat) (up : Bool) (sub : BBTree) -- monotonicity leaf, see §5
  | split (dim : Nat) (l r : BBTree)
deriving Repr

def Box := List Ival
def Box.bisect (B : Box) (d : Nat) : Box × Box
def Box.Mem (B : Box) (xs : List ℝ) : Prop      -- pointwise, same length

/-- property P holds on the whole box -/
def checkBB (c : Ctx) (p : PropExpr) : BBTree → Box → Bool
  | .leaf, B => p.check c ⟨[], B, []⟩
  | .split d l r, B => let (B₁, B₂) := B.bisect d; checkBB c p l B₁ && checkBB c p r B₂
  | .mono d up t, B => monoCheck c p d up B && checkBB c p t (B.face d up)   -- §5

theorem checkBB_sound (hc : c.Valid) (h : checkBB c p t B = true) :
    ∀ xs, B.Mem xs → p.denote ⟨[], xs, []⟩
```

Search (native): depth-first bisection along the widest dimension (or the
dimension with the largest derivative enclosure), leaf when `p.eval3 = yes`,
give up on `no` (counterexample) or when `bbMaxBoxes` is exceeded.  Precision:
start 64 bits, raise if a leaf fails only due to width < 2^-40.

Goal shapes (`Goals/Box.lean`):
* `∀ x ∈ Set.Icc a b, P x` (binder-predicate form), `∀ x, a ≤ x → x ≤ b → P x`,
  nested for several variables (`bilinear_box_le_three`).
* `P x` inside may be any `PropExpr` (the check is 3-valued on each box).

## 3. Ranges `sSup` / `sInf` (`Goals/Range.lean`)

Shape (after unfolding user defs like `rangeSup`):
`|sSup (f '' Set.Icc a b) - ↑p.1| < T₁ ∧ |sInf (f '' Set.Icc a b) - ↑p.2| < T₂`.

For `S = f '' Icc a b` with `a ≤ b` (closed check):
* upper bound: B&B proves `∀ x ∈ [a,b], f x ≤ U` (U dyadic);
* witness point: `x₀ ∈ [a,b]` (native maximization) with `f x₀ ≥ L` (closed check);
* then `sSup S ∈ [L, U]`: `csSup_le (nonempty) (upper bound)` and
  `le_csSup (BddAbove from U) (mem_image_of_mem f hx₀)`.
No continuity is needed.  Choose `p.1 := mid [L, U]` once `U - L < 2·T₁`.
Native search: maximize/minimize by B&B on `f` (keep best lower bound from
point evaluations at box midpoints; prune boxes whose upper bound < best).
Final certificate = the B&B tree for `f ≤ U` (and `f ≥ L'` for inf) + point
checks.

Lemma to write once:

```lean
theorem sSup_image_mem_of_bounds {f : ℝ → ℝ} {a b x₀ L U : ℝ} (hab : a ≤ b)
    (hx₀ : x₀ ∈ Set.Icc a b) (hL : L ≤ f x₀) (hU : ∀ x ∈ Set.Icc a b, f x ≤ U) :
    L ≤ sSup (f '' Set.Icc a b) ∧ sSup (f '' Set.Icc a b) ≤ U
```

## 4. Roots and "no root" answers (`Goals/Root.lean`)

* `{x : ℚ // lo ≤ ↑x ∧ ↑x ≤ hi ∧ |g ↑x| < tol}`: native root search on `g`
  (bisection on sign changes of point enclosures, then secant/Newton with
  float-free dyadic arithmetic; derivative from AD when available), pick a
  short rational `q` with `|g q| < tol/2`; prove `P q` by the closed checker.
* `RootOrNoRoot g lo hi tol` (= `{w // p w} ⊕' ∀ w, ¬ p w`):
  1. try the witness branch (`PSum.inl`);
  2. otherwise prove `∀ w : ℚ, ¬ (lo ≤ ↑w ∧ ↑w ≤ hi ∧ |g ↑w| < tol)` by
     generalizing `↑w` to a real `x` and running B&B on
     `¬ (lo ≤ x ∧ x ≤ hi ∧ |g x| < tol)` over the box `[lo, hi]`
     (outside the box the first conjuncts are false — encode as
     `x ∈ [lo,hi] → |g x| ≥ tol` on the box).
* `InequalityOrNoWitness` identical with the extra conjunct `g x < 0`.

## 5. Automatic differentiation and monotone leaves (`Cert/AD.lean`)

Needed when the bound is attained exactly (`exp_mul_cos_ge_one` at `x = 0`,
`le_sqrt_on_unit` at `x = 0, 1/4, 1`), where no finite subdivision suffices.

Capability per real→real function (in `Fn1`, see 03 §3):

```lean
  dev    : Ctx → Ival → Ival          -- enclosure of F' on X
  dev_ok : ∀ c X x, c.Valid → x ∈ X → (dev c X).isFinite = true →
             ∃ d ∈ dev c X, HasDerivAt fn d x
```

(`Fn2`: `dev₁`, `dev₂` partial derivatives with `HasFDerivAt`-free
formulation: for binary ops we only need `add/sub/mul/div/npow` whose chain
rules are proved directly in the AD evaluator.)

Forward-mode interval AD over one variable `x_d`:

```lean
def Expr.evalAD (c : Ctx) (d : Nat) : Expr .real → IEnv → Ival × Ival   -- (value, derivative)
theorem Expr.evalAD_sound (hc) (hσ : σ ∋ ρ) (e) :
    (e.evalAD c d σ).2.isFinite = true →
    ∀ x ∈ σ.r[d], ∃ D ∈ (e.evalAD c d σ).2, HasDerivAt (fun t => e.denote (ρ.setR d t)) D x
```

Monotone leaf `mono d up t`: if the derivative enclosure of the atom's
difference `R(x) - L(x)` (for atom `L ≤ R`) over the box is `≥ 0`, the minimum
over the box is on the lower face in direction `d` (`MonotoneOn` from
`monotoneOn_of_deriv_nonneg` / `Convex.monotoneOn_of_deriv_nonneg`), so it
suffices to check the face `B.face d false` (a box with `x_d` a point; the
remaining check `t` runs there, typically `leaf` with exact point evaluation:
`exp 0 * cos 0 = 1` is computed exactly because `expPt 0 = [1,1]` and the
π-reduction of `0` with `k = 0` gives the exact point `0`).
Ensure the point kernels return **exact** results on exact inputs where
Mathlib values are rational: `exp 0 = 1`, `cos 0 = 1`, `sin 0 = 0`,
`log 1 = 0`, `sqrt` of perfect squares.

`log_le_sub_one` (unbounded domain `[1, ∞)`) works the same way with an
extended box `[1, +∞]` and the derivative `1/x - 1 ≤ 0` evaluated on the
extended interval (`inv [1, ∞] = [0, 1]`).

## 6. Extrema answers (`Goals/Extrema.lean`)

User definitions (`ApproxGlobalMin`, `IsLocalMinOn`, `ExtremaAnswer`, …) are
unfolded by the generic def-unfolder.  Shapes after unfolding:

* `{x // x ∈ s ∧ ∀ y, y ∈ s → f x ≤ f y + tol} ⊕' …` with `s = Set.Icc (a:ℚ) b`:
  native global minimization (B&B with best-bound pruning) → rational `x*`;
  prove `x* ∈ s` by `norm_num`/`decide` on rationals; prove
  `∀ y ∈ s, f x* ≤ f y + tol` via: `f x* ≤ U` (closed check) and
  `∀ r ∈ [a,b], f r ≥ U - tol` (B&B over reals), then specialize to `r = ↑y`.
* local versions: pick `δ := radius` (so the neighborhood condition is implied
  by the global statement on `s`) — i.e. reduce to the global case on `s`.
* exact (`tol = 0`) and "no extremum" cases (`E01`, `E06–E11`) are
  logical/symbolic: out of scope for interval arithmetic (listed as deferred;
  the procedure must yield on them).

## 7. Milestones

* **M6** B&B + box goals (`Theorems.lean` P21, P23, P24, P27, P29; roots
  `Roots.lean`, `ApproxRoots.lean`).
* **M7** AD + monotone leaves (`Theorems.lean` P22, P25, P26).
* **M8** ranges + extrema (`Ranges.lean`, `Extrema.lean` E02–E05).
