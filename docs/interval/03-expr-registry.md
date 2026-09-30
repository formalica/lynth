# 03 — Typed expressions, function registry, evaluator, reifier

## 1. Value types (`Core/Ty.lean`)

```lean
namespace Lynth.Interval
inductive Ty | nat | real | cplx
deriving Repr, DecidableEq, Inhabited

/-- semantic carrier -/
@[reducible] def Ty.Val : Ty → Type
  | .nat => ℕ | .real => ℝ | .cplx => ℂ
/-- computational enclosure type -/
@[reducible] def Ty.Enc : Ty → Type
  | .nat => NIval | .real => Ival | .cplx => CBox
def Ty.Mem : (t : Ty) → t.Enc → t.Val → Prop
  | .nat, I, n => n ∈ I | .real, I, x => x ∈ I | .cplx, B, z => z ∈ B
def Ty.top : (t : Ty) → t.Enc               -- ⊤ enclosure, `Ty.mem_top`
def Ty.isFinite : (t : Ty) → t.Enc → Bool
-- additive structure needed by the generic `sum` node
def Ty.zeroE : (t : Ty) → t.Enc                 -- exact 0
def Ty.addE  : (t : Ty) → Nat → t.Enc → t.Enc → t.Enc
instance Ty.addCommMonoid : (t : Ty) → AddCommMonoid t.Val   -- by cases
theorem Ty.mem_zero, Ty.mem_add
-- topology / measurability, by cases (used by capabilities)
def Ty.topo : (t : Ty) → TopologicalSpace t.Val
def Ty.meas : (t : Ty) → MeasurableSpace t.Val
```

`Ty.Val`/`Ty.Enc` must reduce by `whnfR` on constructor arguments (they are
reducible matchers), so `Fn1 .real .real` elaborates with `ℝ → ℝ → Prop`.

## 2. Evaluation context (`Core/Ctx.lean`)

```lean
structure Ctx where
  prec : Nat            -- working precision (mantissa bits)
  pi   : Ival           -- enclosure of π at `prec`
  ln2  : Ival           -- enclosure of log 2 at `prec`
deriving Repr

structure Ctx.Valid (c : Ctx) : Prop where
  pi_mem  : Real.pi ∈ c.pi
  ln2_mem : Real.log 2 ∈ c.ln2

def Ctx.make (p : Nat) : Ctx := ⟨p, piIval p, ln2Ival p⟩      -- Fns/Const.lean
theorem Ctx.make_valid (p : Nat) : (Ctx.make p).Valid
```

Constants that many functions need are cached here (computed once per check).
Other constants are `Fn0` records (computed on use).  Adding a cached constant
requires editing `Ctx` (rare; document in `13-progress.md`).

## 3. Function records (`Core/Fn.lean`)

Semantics is stored **only in `Prop`-valued fields** (type formers and proofs
are erased by the compiler), so records containing `Real.exp` etc. are
*computable* and can be used in `native_decide` checks and in meta-goal
runtime functions.

```lean
structure Fn0 (r : Ty) where
  name  : String
  graph : r.Val → Prop
  exu   : ∃! y, graph y
  ev    : Ctx → r.Enc
  sound : ∀ c y, c.Valid → graph y → r.Mem (ev c) y
  cost  : Nat := 1

structure Fn1 (a r : Ty) where
  name  : String
  graph : a.Val → r.Val → Prop          -- canonical form: fun x y => y = F x
  exu   : ∀ x, ∃! y, graph x y
  ev    : Ctx → a.Enc → r.Enc
  sound : ∀ c x y X, c.Valid → graph x y → a.Mem X x → r.Mem (ev c X) y
  cost  : Nat := 1
  -- optional capabilities, all with "not provided" defaults (see phase docs):
  meas    : Bool := false                               -- 07-integrals
  meas_ok : meas = true → Measurable[Ty.meas a, Ty.meas r] (Fn1Core.fn …) := by simp
  cont    : Ctx → a.Enc → Bool := fun _ _ => false      -- continuity on X (06, 09)
  cont_ok : …                                           -- see 06-box-goals §AD/continuity
  dev     : Ctx → a.Enc → r.Enc := fun _ _ => Ty.top r  -- derivative enclosure (06 §AD)
  dev_ok  : …
  conv    : Ctx → a.Enc → Bool := fun _ _ => false      -- convergence domain (09-meta)
  conv_ok : …
  tay     : TayCap a r := TayCap.none                   -- Taylor-model expansion (07)

structure Fn2 (a b r : Ty) where   -- same fields with two arguments
  name graph exu ev sound cost meas meas_ok cont cont_ok dev₁ dev₂ … conv conv_ok tay
```

Because default proof fields need the semantic function, split each record in
`FnXCore` (name, graph, exu, ev, sound, cost) and `FnX extends FnXCore` with
the capability fields that mention `toFnXCore.fn`:

```lean
noncomputable def Fn1Core.fn (f : Fn1Core a r) (x : a.Val) : r.Val := (f.exu x).exists.choose
theorem Fn1Core.fn_spec (f) (x) : f.graph x (f.fn x) := (f.exu x).exists.choose_spec
theorem Fn1Core.graph_iff (f) : f.graph x y ↔ y = f.fn x
```

Convenience constructor (almost every function uses it):

```lean
def Fn1.ofFun (F : a.Val → r.Val) (name : String) (ev : Ctx → a.Enc → r.Enc)
    (sound : ∀ c x X, c.Valid → a.Mem X x → r.Mem (ev c X) (F x)) : Fn1 a r :=
  { name, graph := fun x y => y = F x, exu := fun x => ⟨F x, rfl, fun _ h => h⟩, ev,
    sound := fun c x y X hc hy hx => hy ▸ sound c x X hc hx }
```

`F` only appears inside `graph` (a `Prop`), so `Fn1.ofFun Real.exp …` is
computable.  **Verify this early (M2 smoke test)**: `def expFn := Fn1.ofFun
Real.exp …` must compile without `noncomputable`; if the compiler complains,
mark `F` with `@[inline]`-free lambda inside `graph` only (it already is) and
check that `Fn1.ofFun` itself is `@[inline]`/`@[reducible]` so the compiler
never materializes `F`.

## 4. Environments (`Core/Env.lean`)

Variables are de Bruijn indices **per type**.

```lean
structure SEnv where           -- semantic
  n : List ℕ := []
  r : List ℝ := []
  c : List ℂ := []
def SEnv.get : SEnv → (t : Ty) → ℕ → t.Val      -- getD … 0
def SEnv.push : SEnv → (t : Ty) → t.Val → SEnv  -- cons onto the t-list

structure IEnv where           -- interval
  n : List NIval := []
  r : List Ival := []
  c : List CBox := []
def IEnv.get : IEnv → (t : Ty) → ℕ → t.Enc      -- getD … Ty.top
def IEnv.push …
def SEnv.MemI (σ : IEnv) (ρ : SEnv) : Prop      -- pointwise membership, lengths equal
theorem SEnv.MemI.push : σ ∋ ρ → t.Mem X v → (σ.push t X) ∋ (ρ.push t v)
```

## 5. The AST (`Core/Expr.lean`)

```lean
inductive Expr : Ty → Type where
  | lit    (q : ℚ) : Expr .real                     -- exact rational constant
  | natLit (n : ℕ) : Expr .nat
  | var    (t : Ty) (i : ℕ) : Expr t
  | c0     {r} (f : Fn0 r) : Expr r
  | c1     {a r} (f : Fn1 a r) (x : Expr a) : Expr r
  | c2     {a b r} (f : Fn2 a b r) (x : Expr a) (y : Expr b) : Expr r
  /-- `∑ k ∈ Finset.range n, body` ; body binds a `.nat` variable (index 0) -/
  | sum    (t : Ty) (n : Expr .nat) (body : Expr t) : Expr t
  /-- `∫ y in a..b, body` ; body binds a `.real` variable (index 0); t ∈ {real, cplx} -/
  | integral (t : Ty) (a b : Expr .real) (body : Expr t) (cfg : QuadCfg) : Expr t
```

(`QuadCfg` = pieces/degree chosen by search, stored in the term so the checker
is deterministic; see `07-integrals.md`.)  Further binder nodes (products
`prod`) follow the `sum` pattern.  Rational literals use `ℚ` only as *data*
converted once by `Ival.ofRat` (a single gcd-free division); they never enter
hot loops.

### Denotation (noncomputable)

```lean
noncomputable def Expr.denote : Expr t → SEnv → t.Val
  | .lit q, _ => (q : ℝ)
  | .natLit n, _ => n
  | .var t i, ρ => ρ.get t i
  | .c0 f, _ => f.val                                   -- Fn0Core.val via choose
  | .c1 f x, ρ => f.fn (x.denote ρ)
  | .c2 f x y, ρ => f.fn (x.denote ρ) (y.denote ρ)
  | .sum t n body, ρ => ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)
  | .integral t a b body _, ρ => ∫ y in a.denote ρ..b.denote ρ, body.denote (ρ.push .real y)
```

(`sum`/`integral` need `Ty`-generic `AddCommMonoid`/`NormedAddCommGroup` +
`NormedSpace ℝ` instances; provide them by cases in `Core/Ty.lean`, and make
`integral` well-typed only for `t ∈ {real, cplx}` via a helper
`Ty.intg : (t : Ty) → (ℝ → t.Val) → ℝ → ℝ → t.Val` that is `0` for `.nat`.)

### Evaluation (computable, kernel-reducible, structural recursion)

```lean
def Expr.eval (c : Ctx) : Expr t → IEnv → t.Enc
  | .lit q, _ => Ival.ofRat c.prec q
  | .natLit n, _ => NIval.pt n
  | .var t i, σ => σ.get t i
  | .c0 f, _ => f.ev c
  | .c1 f x, σ => f.ev c (x.eval c σ)
  | .c2 f x y, σ => f.ev c (x.eval c σ) (y.eval c σ)
  | .sum t n body, σ =>
      match (n.eval c σ).isPoint with
      | some N => sumLoop c t body σ N          -- structural on N, accumulates with Ty.addE
      | none   => Ty.top t                      -- (Phase 6/7 refine: ranges of n)
  | .integral t a b body q, σ => Quad.eval c t (a.eval c σ) (b.eval c σ) body σ q   -- 07
```

### Generic soundness (proved once)

```lean
theorem Expr.eval_sound {c : Ctx} (hc : c.Valid) :
    ∀ {t} (e : Expr t) {ρ : SEnv} {σ : IEnv}, σ ∋ ρ → t.Mem (e.eval c σ) (e.denote ρ)
```

Proof: induction on `e`; `c1` case is `f.sound c _ _ _ hc (f.fn_spec _) ih`;
`sum` case by induction on `N` with `Finset.sum_range_succ` and `Ty.mem_add`;
`integral` case delegates to `Quad.eval_sound` (07).

## 6. Propositions (`Core/Prop.lean`)

```lean
inductive PropExpr where
  | lt (a b : Expr .real) | le (a b : Expr .real) | ne (a b : Expr .real)
  | and (p q : PropExpr) | or (p q : PropExpr) | not (p : PropExpr) | imp (p q : PropExpr)
  | tt | ff
noncomputable def PropExpr.denote : PropExpr → SEnv → Prop
inductive Tri | yes | no | unk
def PropExpr.eval3 (c : Ctx) : PropExpr → IEnv → Tri
  -- lt: yes if (a.eval).hi < (b.eval).lo ; no if (b.eval).hi ≤ (a.eval).lo ; else unk
theorem PropExpr.eval3_sound (hc : c.Valid) (hρ : σ ∋ ρ) :
    (p.eval3 c σ = .yes → p.denote ρ) ∧ (p.eval3 c σ = .no → ¬ p.denote ρ)
def PropExpr.check (c) (p) (σ) : Bool := p.eval3 c σ == .yes
```

Real-valued comparisons of complex data are expressed through real-valued
`Fn1 .cplx .real` nodes (`re`, `im`, `norm`), so atoms stay real.

## 7. Registry (`Reify/Registry.lean`)

```lean
structure FnEntry where
  decl    : Name         -- constant of type Fn0 r / Fn1 a r / Fn2 a b r
  arity   : Nat          -- 0,1,2
  argTys  : Array Ty
  resTy   : Ty
  pattern : Lean.Expr    -- term with loose bvars #0..#(arity-1) = arguments
  prio    : Nat := 1000
initialize fnExt : SimpleScopedEnvExtension FnEntry (DiscrTree FnEntry)
syntax (name := lynthFnAttr) "lynth_fn" (ppSpace num)? (ppSpace term)? : attr
```

Attribute handler:
1. Infer arity/types from the declaration type (`Fn1 .real .real` → `whnfD` the
   `Ty` args to constructors).
2. If an explicit pattern term is given (`@[lynth_fn (Real.cosh ?x)]`) use it.
   Otherwise **derive it from `graph`**: unfold `decl.graph` (`whnfD`,
   `Fn1.ofFun` unfolds), `lambdaTelescope` it to `fun x₁ … y => y = P`,
   check the body is `Eq y P`, and abstract `x₁…` in `P`.
3. Insert into the DiscrTree with keys `DiscrTree.mkPath P'` where `P'` has
   fresh mvars for the arguments (reducible transparency, `instances` for
   instance arguments, so `@HAdd.hAdd ℝ ℝ ℝ instHAdd x y` matches).
4. Several entries may match a term (e.g. `x ^ (n:ℕ)` vs `x ^ (y:ℝ)`): try in
   descending `prio`, first successful reification wins.

## 8. Reifier (`Reify/Reify.lean`)

```lean
structure Reified where
  ty    : Ty
  expr  : Lean.Expr      -- : Lynth.Interval.Expr ty
  proof : Lean.Expr      -- : orig = Expr.denote expr ρ
structure RCtx where
  senv   : Lean.Expr                     -- SEnv term ρ
  vars   : Array (Lean.Expr × Ty × Nat)  -- (fvar or atom term, type, de Bruijn index)
  atoms  : Bool                          -- allow opaque atoms as new variables
  depth  : Nat                           -- unfolding budget
partial def reify (rc : RCtx) (t : Ty) (e : Lean.Expr) : ReifyM Reified
```

Steps for a term `e` expected at type `t` (first success wins):

1. **Variable**: `e` is (syntactically, after `instantiateMVars`) one of
   `rc.vars` → `var t i`, proof `rfl`.
2. **Exact constant** (`Reify/Exact.lean`): if `e` has no fvars/mvars and its
   head is arithmetic/cast/ℕ-function (not a registered transcendental), try
   `Mathlib.Meta.NormNum.derive` (plus the `lynth_exact` simp set for
   polynomial evaluations: Chebyshev `T/U`, `Polynomial.bernoulli`,
   `ascPochhammer`, `bernoulli`, `Nat.bell`); success → `lit q` (or `natLit n`)
   with proof of `e = ((q:ℚ):ℝ)` produced by the `norm_num` result
   (`Result.toRawEq` + `Rat.cast` normalization).  Complex closed rationals
   → `c1 ofRealFn (lit q)`.
3. **Binders**: `Finset.sum (Finset.range n) (fun k => b)` → reify `n` at
   `.nat`, then `withLocalDecl k`, push `(k, .nat)` into vars (shifting nat
   indices), reify `b`; proof via
   `Finset.sum_congr (congrArg _ hn) (fun k _ => hb k)` (`hb` is a lambda
   proof over the local `k`).  Integrals analogous (07).
4. **Registry**: `DiscrTree.getMatch e` → for each candidate: instantiate the
   pattern with fresh mvars, `isDefEq` (reducible + instances), reify the
   arguments at `argTys`, build the node.  Proof uses

   ```lean
   theorem Expr.c1_eq (f : Fn1 a r) (x : Expr a) (ρ : SEnv) {X : a.Val} {Y : r.Val}
       (hX : X = x.denote ρ) (hY : f.graph X Y) : Y = (Expr.c1 f x).denote ρ
   ```

   with `hY := Eq.refl Y` (accepted because `f.graph X Y` unfolds to `Y = F X`
   and `Y` *is* `F X` syntactically).  Same for `c0`, `c2`.
5. **Unfold**: if the head is a constant with a definition that is not in the
   registry (user definitions such as `quinticResidual`, `rangeSup`,
   `extremaTolerance`), `delta`-unfold once (`unfoldDefinition?`), `headBeta`,
   and retry (budget `rc.depth`).  Never unfold `Real.exp` & co (they are in
   the registry and matched in step 4 first).
6. **Atom**: if `rc.atoms`, any remaining term of type ℝ/ℂ/ℕ becomes a fresh
   variable (the caller must supply its enclosure, e.g. from hypotheses).
7. Otherwise fail with a message naming the unsupported head.

The reifier also returns the **runtime value** of the reified expression when
needed: `evalExpr (Expr t) (mkApp (Expr) (toExpr t)) r.expr` (function records
are compiled constants, so this is fast and native).

## 9. How to add a new function (the only thing contributors touch)

1. Create `Lynth/Interval/Fns/MyFn.lean`:

```lean
import Lynth.Interval.Core.Fn
import Lynth.Interval.Series.Horner   -- if needed
namespace Lynth.Interval.Fns

/-- interval extension on extended intervals; return `Ival.top` when unsure -/
def coshIval (c : Ctx) (X : Ival) : Ival := …

theorem coshIval_sound {c : Ctx} (hc : c.Valid) {x : ℝ} {X : Ival} (hx : x ∈ X) :
    Real.cosh x ∈ coshIval c X := …

@[lynth_fn] def coshFn : Fn1 .real .real :=
  { Fn1.ofFun Real.cosh "cosh" coshIval (fun c x X hc hx => coshIval_sound hc hx) with
    meas := true, meas_ok := fun _ => Real.continuous_cosh.measurable
    -- optional: cont/dev/conv/tay capabilities
  }
```

2. Add `import Lynth.Interval.Fns.MyFn` to `Fns/All.lean`.
3. Add a test in `Test/Interval/Fns.lean` (`#eval` enclosure + one `lynth` goal).

Rules: the interval extension must be sound for **every** input (return ⊤ when
in doubt — e.g. outside the domain where Mathlib's junk value is hard to
bound); precision comes from `c.prec`; no well-founded recursion.

Derived functions (defined by an identity with registered ones, e.g.
`tan = sin / cos`, `logb b x = log x / log b`) can reuse the generic
constructor

```lean
def Fn1.ofExpr (F : ℝ → ℝ) (body : Expr .real)   -- body uses var .real 0
    (h : ∀ x, F x = body.denote (SEnv.push {} .real x)) : Fn1 .real .real
```

whose `ev` evaluates `body` and whose soundness is `Expr.eval_sound` + `h`.
