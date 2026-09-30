# 01 — Architecture

## 1. Layers

```
 user goal (Lean term)
   │
   ▼
 Goals/*          goal-shape handlers (DiscrTree-registered): recognize shape,
   │              call search, build final proof from a soundness theorem
   ▼
 Reify/*          Lean term  ──►  (e : Expr t, proof : term = e.denote ρ)
   │              + exact evaluator for closed ℕ/ℤ/ℚ subterms (norm_num/simp)
   ▼
 Core/*           Ty, Ctx, Fn0/Fn1/Fn2 records, Expr AST, denote, eval,
   │              eval_sound (generic), PropExpr (∧ ∨ ¬ < ≤ atoms)
   ▼
 Fns/*            one file per function family: registry entries
   │              (graph, interval extension, soundness, optional capabilities)
   ▼
 Series/*         generic "polynomial + remainder" toolkit (interval Horner,
   │              geometric tail bounds) shared by function implementations
   ▼
 Num/*            Dy (dyadic), rounding, Ival (extended), NIval, CBox, proofs
   ▼
 Vendor/*         adapted LeanCert proofs (Apache-2.0)

 Cert/*           certificate checkers + soundness theorems:
                  Point (closed props), BB (branch&bound trees), AD,
                  TM (Taylor models), Integral, Series (tails), Meta (conv.)
 Check/*          trust driver: kernel (`Eq.refl true` checked by kernel) /
                  native (`native_decide`) / auto (cost model)
```

## 2. Module layout (files to create)

```
Lynth/Interval/
  Vendor/Dyadic.lean            -- from LeanCert Core/Dyadic.lean (renamed ns)
  Vendor/TaylorBounds.lean      -- from LeanCert Core/IntervalRat/Taylor.lean (subset)
  Vendor/SqrtBounds.lean        -- from LeanCert Core/IntervalRat/Transcendental.lean (subset)
  Num/Dy.lean                   -- Dy API on top of vendored Dyadic: toReal, roundDown/Up p,
                                   ofRatDown/Up, divDown/Up, sqrtDown/Up, pow2, bits, lemmas
  Num/Ival.lean                 -- extended intervals + FTIA ops (add neg sub mul inv div sq npow abs
                                   min max hull bisect ofRat ofDy width mid) with proofs
  Num/NIval.lean                -- ℕ intervals (lo, optional hi) + ops
  Num/CBox.lean                 -- complex rectangles + ops (add neg mul inv div ofReal re im conj
                                   normSq norm) with proofs
  Core/Ty.lean                  -- Ty, Ty.Val, Ty.Enc, Ty.Mem, per-Ty zero/add/top, instances
  Core/Ctx.lean                 -- Ctx (prec, cached π, ln2), Ctx.Valid, Ctx.make, make_valid
  Core/Fn.lean                  -- Fn0 / Fn1 / Fn2 records (+ capability fields), fn, fn_spec
  Core/Env.lean                 -- SEnv (semantic), IEnv (interval), push/get, SEnv.Mem
  Core/Expr.lean                -- Expr AST, denote, eval, eval_sound
  Core/Prop.lean                -- PropExpr AST (atoms/∧/∨/¬/→), denote, 3-valued check, sound
  Series/Horner.lean            -- interval Horner, polynomial-with-remainder lemma
  Series/Tail.lean              -- geometric tail bounds for HasSum series
  Fns/Arith.lean                -- + - * neg inv / npow zpow abs min max, casts ℕ→ℝ, ℝ→ℂ
  Fns/Const.lean                -- π (Machin), ln 2, e, I
  Fns/Exp.lean  Fns/Log.lean  Fns/Sqrt.lean  Fns/Trig.lean  Fns/Arctan.lean
  Fns/InvTrig.lean (arcsin arccos)   Fns/Hyperbolic.lean (sinh cosh tanh arsinh arcosh artanh)
  Fns/Pow.lean (rpow, logb)     Fns/Sinc.lean   Fns/Nat.lean (factorial fib choose succ …)
  Fns/Complex.lean              -- complex exp log sin cos sinh cosh cpow sqrt arg norm re im conj
  Fns/All.lean                  -- imports every Fns file (the registry is populated by import)
  Reify/Registry.lean           -- @[lynth_fn] attribute, DiscrTree env extension
  Reify/Exact.lean              -- closed ℕ/ℤ/ℚ/ℝ-rational subterm evaluation (norm_num, simp set)
  Reify/Reify.lean              -- term → Expr + denote proof; atoms → variables
  Reify/PropReify.lean          -- Prop → PropExpr + proof
  Cert/Point.lean               -- checkProp, precision search, witness choice
  Cert/BB.lean  Cert/AD.lean  Cert/TM.lean  Cert/Integral.lean  Cert/Tail.lean  Cert/Conv.lean
  Check/Trust.lean              -- Trust mode, cost model, `certify` (kernel/native)
  Goals/Approx.lean             -- {x : ℚ // P x}, {p : ℚ × ℚ // …}, complex shapes
  Goals/Closed.lean             -- closed props: A < B, |A - B| < T, ∧/∨ …
  Goals/Discrete.lean           -- ⌊E⌋₊, ⌈E⌉₊, ⌊E⌋, Real.sign, ℕ/ℤ-valued closed computations
  Goals/Box.lean  Goals/Range.lean  Goals/Root.lean  Goals/Extrema.lean
  Goals/Integral.lean  Goals/Series.lean  Goals/Meta.lean
  Procedure.lean                -- `Lynth.Interval.Procedure.run : TacticM ProcedureOutcome`
Lynth/Interval.lean             -- umbrella import (added to Lynth.lean)
```

`Lynth.lean` gets `import Lynth.Interval`.  All `Lynth/Interval` modules are
built with `precompileModules = true` (already set for the `Lynth` library), so
search code runs natively in the elaborator.

## 3. Data flow for one goal

1. `Procedure.run` inspects the main goal type (after `instantiateMVars`,
   `whnfR`, and unfolding of *non-registry* user definitions up to a depth
   limit), and tries goal handlers in priority order (a DiscrTree keyed by the
   goal head: `Subtype`, `PSum`, `And`, `LT.lt`, `LE.le`, `Not`, `∀`, …).
2. The handler reifies the relevant subterms (Reify) into `Expr`/`PropExpr`
   *terms* together with equality proofs `orig = e.denote ρ`, and also obtains
   the *runtime value* of each `Expr` (via `evalExpr` on the reified term;
   function records are compiled constants, so this runs native code).
3. Search (native): choose precision / subdivision / witness / N / pieces.
4. Certificate: a closed Bool term `check args = true`, discharged by the trust
   driver (`Check/Trust.lean`).
5. Final proof: `soundness_theorem args (h : check args = true) … : goal`,
   rewritten along the reification equalities; assigned with `closeMainGoal`.
6. Any failure → restore state, return `.failure []` (yield).

## 4. Integration into `lynth`

* `Lynth/Frontend.lean`: add `("interval", Lynth.Interval.Procedure.run)` right
  after `("meta", …)` and **before** `finsearch`/`witness` (those waste time on
  real goals).  The procedure first runs a cheap *relevance gate*: the goal
  mentions `Real`, `Complex`, `ℝ`-valued `tsum`/integral, or `Rat`-valued
  subtype whose predicate mentions `ℝ`; otherwise it yields immediately.
* `answer` procedure: for `PSum` goals the interval procedure handles the split
  itself (`Goals/*` recognize `A ⊕' B` shapes with interval content), so it
  must run before `answer`; place it **first** in the list, gated by relevance.
* Config: `lynth` gains an optional config (`Lynth/Basic.lean`):

```lean
structure Lynth.Config where
  trust        : Lynth.Interval.Trust := .auto   -- .kernel | .native | .auto
  maxPrec      : Nat := 8192          -- bits, upper limit for precision search
  kernelBudget : Nat := 2000000       -- cost-model units allowed in kernel mode (auto)
  bbMaxBoxes   : Nat := 4096          -- branch & bound leaf limit
  timeLimitMs  : Nat := 55000         -- soft limit for interval search
declare_config_elab elabLynthConfig Lynth.Config
syntax (name := lynthTac) "lynth" optConfig : tactic
```

  Usage: `by lynth`, `by lynth (trust := .kernel)`, `by lynth +native`?  (Use
  `(trust := .native)`; boolean shorthands are optional.)  Also a global
  option `set_option lynth.interval.trust "kernel"` read when the config field
  is left default (options are easier for whole test files).
  `Frontend.dispatch` takes the config and stores it in a `ReaderT`/`IO.Ref`
  (`Lynth.Interval.currentConfig`) readable by the procedure.

## 5. Trust modes (`Check/Trust.lean`)

All certificates have the form `check (args) = true` with a generic soundness
theorem.  Discharging:

```lean
inductive Trust | kernel | native | auto deriving Repr, DecidableEq, Inhabited

/-- Prove `lhs = true` where `lhs : Bool` is closed. -/
def certify (trust : Trust) (lhs : Lean.Expr) (cost : Nat) : MetaM Lean.Expr := do
  let goalTy ← mkEq lhs (mkConst ``Bool.true)
  match effective trust cost with
  | .kernel =>
      -- auxiliary theorem whose value is `Eq.refl true`; the kernel evaluates `lhs`
      let pf := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
      mkAuxTheorem goalTy pf (zetaDelta := false)       -- or Lean.Meta.mkAuxLemma
  | .native =>
      -- run the `native_decide` tactic on an mvar of type `goalTy`
      let m ← mkFreshExprMVar goalTy
      let [] ← Lean.Elab.Term.TermElabM.run' (Lean.Elab.Tactic.run m.mvarId! (evalTactic (← `(tactic| native_decide))))
      instantiateMVars m
```

* Before calling the kernel, **always run the check natively first**
  (`evalExpr Bool` on `lhs`) — if it is `false`, do not send it to the kernel.
* Kernel-evaluated code must avoid well-founded recursion (the kernel cannot
  unfold `WellFounded.fix` efficiently): use structural recursion or explicit
  `fuel : Nat` arguments everywhere in `Num/`, `Core/`, `Fns/`, `Cert/`.
  `Nat.find`/WF is allowed only in *meta-goal runtime code* that is never
  reduced by the kernel (Phase 7).
* Avoid `Rat` in hot kernel paths (gcd normalization); use `Dy`.
* `auto`: `effective .auto cost = if cost ≤ cfg.kernelBudget then .kernel else .native`.
  `cost` comes from a static cost model: `Expr.cost (p : Nat) : Expr t → Nat`
  (per node `Fn.cost` field (default 1) × `(p/64+1)^2`, sums × n, integrals ×
  pieces × degree², BB × leaves).  Calibrate `kernelBudget` so that a kernel
  check stays ≲ 30 s (measured: ≈ 4000 Taylor steps/s at 200 bits).
* Test files pin axioms; tests run with default config.  If a test needs native
  checking under `auto`, its pin lists the auxiliary native axiom.

## 6. Relevance gate & recognition order (`Procedure.lean`)

```
run := do
  unless (← relevant) do return .failure []
  for h in handlers (priority order) do
    match ← withRestore (h.run cfg) with
    | .closed => return .success
    | .notApplicable | .failed _ => continue
  return .failure []
```

Handler priority (first match wins): Meta (function-valued subtypes) →
Series (`Summable`/`tsum`) → Integral → Range (`sSup`/`sInf`) → Extrema/Root
answers (`PSum`) → Discrete (`⌊⌋₊`, `sign`) → Approx (`{x : ℚ // …}`,
`{p : ℚ × ℚ // …}`, complex shapes) → Box (`∀ x ∈ Icc …`) → Closed props.

## 7. Error reporting

Every handler logs (trace class `lynth.interval`) the recognized shape, chosen
precision, cost and trust mode; failures carry a short reason string so the
final `lynth` error lists e.g. `interval: Approx: enclosure too wide at 8192 bits`.
Register `initialize registerTraceClass `lynth.interval`.
