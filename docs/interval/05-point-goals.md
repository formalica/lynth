# 05 — Point goals (Phases 1 and 3)

## 1. Closed propositions (`Cert/Point.lean`, `Goals/Closed.lean`)

Any goal `P` that is a closed proposition built from `<`, `≤`, `>`, `≥`, `≠`
between real-valued terms, `|·|`, `∧`, `∨`, `¬`, `→` is handled by:

1. `PropReify`: `P ↦ (p : PropExpr, h : P ↔ p.denote SEnv.nil)` (congruence
   through connectives; `a > b` is `b < a`; `|A - B| < T` stays an atom
   `lt (c1 absFn (c2 subFn A B)) T`).
2. Precision search (native): `for p in [64, 128, 256, …, cfg.maxPrec]`:
   `if (p.check (Ctx.make p) IEnv.nil) then break`.
3. Certificate: `PropExpr.check (Ctx.make p) pE IEnv.nil = true` via `certify`.
4. Proof: `(h.mpr (PropExpr.check_sound (Ctx.make_valid p) SEnv.MemI.nil hcert))`.

```lean
theorem PropExpr.check_sound {c : Ctx} (hc : c.Valid) {σ ρ} (hρ : σ ∋ ρ) {p : PropExpr}
    (h : p.check c σ = true) : p.denote ρ
```

Covers: `gamma_bounds` (once Gamma exists), `series_inv_sq_tail` (finite sum
of 1000 terms vs `π^2/6`), `alternating_series_pi_over_four`, and every
intermediate obligation produced by other handlers (floor bounds, witness
checks, …).

## 2. Rational witnesses `{x : ℚ // P x}` (`Goals/Approx.lean`)

Recognized after `whnfR` + user-def unfolding: `Subtype (fun x : ℚ => P x)`
where `P` mentions `x` only through `((x : ℚ) : ℝ)` (and possibly `(x : ℝ)`
coerced into `ℂ`).  Also `{p : ℚ × ℚ // P p}` (components via `p.1`, `p.2`),
`{v : Fin n → ℚ // …}` (later), and `{x : ℚ // P x}` where `P` is a root
condition (see 06 §4).

Witness guessing (native, untrusted):
* collect *anchor terms*: for every atom of shape `|A - ↑x| ⋈ T`,
  `|↑x - A| ⋈ T`, `A - ↑x ⋈ T`, `dist A ↑x ⋈ T` record `A` (closed);
  for `p.1`/`p.2` record per component.
* evaluate each anchor at increasing precision; candidate `x := short rational
  inside mid ± (tolLo/4)` (continued-fraction/decimal shortening: take the
  shortest decimal with `d` digits inside the interval, `d` increasing).
* if no anchor exists (e.g. `|x^3 - 2| < 1e-7`), fall back to the root finder
  (06 §4) on the atoms containing `x`.
* instantiate `P q`, reify as a *closed* proposition (the literal
  `((q:ℚ):ℝ)` reifies to `lit q` with proof `rfl`-level `Rat.cast` equality),
  run §1.  If the check fails at `maxPrec`, try the next candidate.
* Proof term: `⟨q, proof_of_P_q⟩`.

The same code handles tolerances that are real expressions (`Real.pi / 100`,
`(10:ℝ)^(-10:ℤ)`), because `T` is just another reified subterm.

## 3. Discrete answers (`Goals/Discrete.lean`)

| goal | witness | reduction to closed props |
|---|---|---|
| `{n : ℕ // n = ⌊E⌋₊}` | `n := ⌊mid E⌋` | `Nat.floor_eq_iff (ha : 0 ≤ a) : ⌊a⌋₊ = n ↔ ↑n ≤ a ∧ a < ↑n + 1`; if the enclosure is negative use `Nat.floor_eq_zero.mpr (a < 1)` |
| `{n : ℕ // n = ⌈E⌉₊}` | `n := ⌈mid E⌉` | `Nat.ceil_eq_iff (hn : n ≠ 0) : ⌈a⌉₊ = n ↔ ↑(n - 1) < a ∧ a ≤ ↑n`; `n = 0` via `Nat.ceil_eq_zero` |
| `{n : ℤ // n = ⌊E⌋}` / `⌈E⌉` | analogous | `Int.floor_eq_iff`, `Int.ceil_eq_iff` |
| `{s : ℤ // Real.sign E = (s:ℝ)}` | sign of enclosure | `Real.sign_of_neg`, `Real.sign_of_pos` (zero only if `E` reifies to exact 0) |
| `{n : ℕ // n = e}` with `e : ℕ` closed computable | evaluate `e` natively (`evalExpr ℕ`) | `⟨lit, by decide⟩` (`Nat.decEq`, kernel; keeps *zero axioms* as pinned for `gcd_of_fib`) |

Orientation variants (`⌊E⌋₊ = n`) are normalized by `Eq.symm`.

## 4. Finite sums (Phase 3, `Core/Expr.lean` `sum` node)

Reification of `∑ k ∈ Finset.range n, f k` (also `Finset.sum (Finset.range n)
fun k => …` with any binder name, and `∑ i : Fin n, f i` rewritten by
`Fin.sum_univ_eq_sum_range`).  `n` must evaluate to a point `NIval`; the
evaluator loops `k = 0 … n-1` (structural recursion on the `Nat` literal).
Soundness: induction with `Finset.sum_range_succ`.

Performance: at 1000 terms (`series_inv_sq_tail`) the kernel check is ~1000 ×
(few mults + 1 division).  If `cost > kernelBudget` under `auto`, native.

`Finset.sum` over other finsets (`Finset.Icc a b`, `Finset.Ico`) → rewrite with
`Finset.sum_Ico_eq_sum_range` first (simp lemma set `lynth_sum_norm`).

Products `∏ k ∈ range n` analogous (node `prod`, add when a test needs it).

## 5. Prod / vector witnesses

`{p : ℚ × ℚ // P p.1 p.2}`: anchors per component (ranges: `|rangeSup … - p.1|`
→ anchor `rangeSup …` which is handled by 06 §3 *inside* a closed check — the
closed checker cannot evaluate `sSup`, so the Range handler must run first on
such goals; see 06 §3).  Linear-system witnesses (`linear_system_witness`) are
deferred (linear algebra).

## 6. Certificate size and search limits

* precision schedule: `64, 96, 128, 192, 256, 384, 512, …` up to `maxPrec`.
* stop search when `timeLimitMs` is exceeded → yield with reason.
* kernel checks must use the **smallest** precision that succeeded.

## 7. Milestones

* **M1** Num layer (02).  **M2** Core (Ty/Ctx/Fn/Expr/eval_sound/PropExpr).
* **M3** Registry + reifier + exact evaluator + arithmetic + constants + exp/log/sqrt.
* **M4** trig, arctan, inverse trig, hyperbolic, rpow, logb, sinc; `Basic.lean`
  and all non-special Compositions tests green (kernel mode).
* **M5** discrete + finite sums: `Discrete.lean` (non-Gamma), `Sums.lean`
  T12–T14 + B01/B03, `Special.lean` T20 + B06.
