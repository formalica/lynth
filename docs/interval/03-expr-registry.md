# 03 — Typed expressions, function registry, evaluator, reifier

## 1. Value types (`Core/Ty.lean`)

```lean
namespace Lynth.Interval
inductive Ty | nat | int | real | cplx | rat | list (t : Ty)
deriving Repr, DecidableEq, Inhabited

/-- semantic carrier -/
@[reducible] def Ty.Val : Ty → Type
  | .nat => ℕ | .int => ℤ | .real => ℝ | .cplx => ℂ
  | .rat => ℚ | .list t => List t.Val
/-- computational enclosure type -/
@[reducible] def Ty.Enc : Ty → Type
  | .nat => NIval | .int => ZIval | .real => Ival | .cplx => CBox
  | .rat => Option ℚ | .list t => Option (List t.Enc)
def Ty.Mem : (t : Ty) → t.Enc → t.Val → Prop
  | .nat, I, n => n ∈ I | .real, I, x => x ∈ I | .cplx, B, z => z ∈ B
  | .rat, o, v => ∀ q, o = some q → v = q
  | .list _, none, _ => True
  | .list t, some X, v => List.Forall₂ (Ty.Mem t) X v
def Ty.top : (t : Ty) → t.Enc               -- ⊤ enclosure, `Ty.mem_top`
def Ty.isFinite : (t : Ty) → t.Enc → Bool
-- additive structure needed by the generic `sum` node
def Ty.zeroE : (t : Ty) → t.Enc                 -- exact 0
def Ty.addE  : (t : Ty) → Nat → t.Enc → t.Enc → t.Enc
instance Ty.addCommMonoid : (t : Ty) → AddCommMonoid t.Val   -- by cases
theorem Ty.mem_zero, Ty.mem_add
```

`Ty` is the single type index: custom-function positions are typed by `Ty`
directly (there is no separate `CTy`). `.rat` positions carry exact values
(`Option ℚ`, unresolved is `none`) and are reified from closed rational
terms; `.list t` positions carry pointwise enclosures (`none` is top).
`Ty.Val`/`Ty.Enc` must reduce by `whnfR` on constructor arguments (they are
reducible matchers).

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
  | rlit   (q : ℚ) : Expr .rat                      -- exact rational (`.rat` positions)
  | natLit (n : ℕ) : Expr .nat
  | intLit (z : ℤ) : Expr .int
  | clist  {t : Ty} (xs : ExprList t) : Expr (.list t)  -- list literal
  | var    (t : Ty) (i : ℕ) : Expr t
  | call   {tys : List Ty} {r : Ty} (f : CFn tys r) (xs : CArg tys) : Expr r
  /-- `∑ k ∈ Finset.range n, body` ; body binds a `.nat` variable (index 0) -/
  | sum    (t : Ty) (n : Expr .nat) (body : Expr t) : Expr t
```
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
structure NaryEntry where
  decl    : Name         -- constant of type `CFn tys r` (or `Fn0`/`Fn1`/`Fn2`)
  tys     : Array Ty
  res     : Ty
  cfn     : Lean.Expr    -- `CFn` value term for call nodes
  pattern : Lean.Expr    -- applicative pattern for `DiscrTree` matching
  keys    : Array DiscrTree.Key
  prio    : Nat := 1000
initialize naryExt : SimpleScopedEnvExtension NaryEntry (DiscrTree NaryEntry)
syntax (name := lynthCfnAttr) "lynth_cfn" (ppSpace num)? : attr
```

One unified table. `@[lynth_cfn]` accepts a `CFn tys r` definition
(pattern from the Lean function `F`, read from `graph` first so entries
can keep a computable `fn` placeholder while a noncomputable mirror lives
only in `Prop` fields) or an `Fn0`/`Fn1`/`Fn2` record (pattern from the
`graph` RHS, call nodes via the `CFn.ofFn0`/`ofFn1`/`ofFn2` lift, whose
`fn` is a dummy — denotation uses `fn'`, evaluation uses `ev`).
Domain checks read each position as a `Ty` (structural, incl. `.list`).
Priorities order candidates; first successful reification wins.


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
2. **Exact constant**: if `e` has no fvars/mvars and its head is not a
   registered transcendental, try `Mathlib.Meta.NormNum.derive` (plus the
   `lynth_exact` simp set); success → `lit q` / `natLit n` / `intLit z` /
   `rlit q` with proof of the value equation.  Complex closed rationals
   normalize to `Complex.ofReal ↑q` and delegate to the `ofRealC` entry.
   2b. **List literals**: closed `List.cons`/`List.nil` spines reify
   elementwise into `Expr.clist` (via `ExprList`), proofs folded with
   `clist_nil_eq`/`clist_cons_eq`.
   2c. **Multiset `HGFun`**: `Complex.HGFun a b z` over literal spines
   normalizes both multisets to lists (`msToList?`, kernel-checked `rfl`s)
   and delegates to the single `HGFunL` entry; bridge proof by `rfl`.
3. **Binders**: `Finset.sum (Finset.range n) (fun k => b)` → reify `n` at
   `.nat`, then `withLocalDecl k`, push `(k, .nat)` into vars (shifting nat
   indices), reify `b`.
4. **Registry** (single unified table): `DiscrTree.getMatch e` → for each
   candidate: instantiate the pattern with fresh mvars, `isDefEq`
   (reducible + instances), reify each argument at its position type
   (`.rat` positions take the closed `ℚ` term directly to `Expr.rlit`),
   build `CArg`/`CVal` chains with proofs (`call_eq`, kernel-checked on
   the spot). `.rat` results never reach `tryNary`; `↑q` with closed `q`
   reifies via `reifyRatCast?` to `Expr.lit q` (sound by `rfl`).
5. **Unfold**: if the head is a constant with a definition that is not in the
   registry, `delta`-unfold once and retry (budget `rc.depth`).
6. **Atom**: if `rc.atoms`, any remaining term becomes a fresh variable.
7. Otherwise fail with a message naming the unsupported head.

The reifier also returns the **runtime value** of the reified expression when
needed: `evalExprVal` (entries must be computable — noncomputable mirrors
live only in `Prop` fields, per the `Fn.lean` rule).


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

## 10. Custom functions (`CFn`, `@[lynth_cfn]`) and multiset `HGFun`

All functions — built-in `Fn0`/`Fn1`/`Fn2` records and n-ary customs —
register through the single `@[lynth_cfn]` attribute as `CFn tys r` entries
(`tys : List Ty`, arbitrary length and mixed positions). `Fn` records lift
via `CFn.ofFn0`/`ofFn1`/`ofFn2` (graph/exu/ev/sound preserved; `fn` is a
dummy — denotation uses `fn'`, evaluation uses `ev`; asymptotics default
to `⊤`).

```lean
structure CFn (tys : List Ty) (r : Ty) where
  name  : String
  fn    : curriedType tys r        -- placeholder (never applied)
  graph : CVal tys → r.Val → Prop   -- exact-value relation
  exu   : ∀ xs, ∃! y, graph xs y
  ev    : Ctx → CEnc tys → r.Enc
  sound : ∀ c vs ds y X, c.Valid → graph vs y →
    CEncHolds X ds → Agree vs ds → r.Mem (ev c X) y
```

Two constructors: `CFn.ofFn` (automatic; discrete results via
`evOfNat`/`evOfInt`/`evOfRat` on `resolveExact`, other results widen to
`⊤`) and `CFn.manual` (user supplies `ev` + `sound` against the automatic
`graphOf`). Both fix `graph := graphOf`, so functionality is automatic.

Noncomputable mirrors: keep the real function only in `graph`/`exu`/`sound`
(`Prop`) with a computable dummy `fn`; the registry reads `F` from `graph`
(`CFn.graphOf tys r F`) first. Entries must stay computable or
`evalExprVal` cannot evaluate them.

Generalized hypergeometric: goals write multiset `Complex.HGFun`; one
`HGFunL : List ℂ → List ℂ → ℂ → ℂ` entry (`Fns/Hypgeom.lean`, FLINT
`pfq_direct` core) serves all shapes. Multiset literals normalize to lists
(`msToList?`); the bridge `HGFun a b z = HGFunL na nb z` is definitional.
Analytic bounds live in `/tmp/pfq_thm_proof.lean` (Mathlib-only handoff).

Suite: `Test/Interval/Nary.lean` N1–N10 plus `Test/Interval/Hypgeom.lean`
H1–H14 (multiset `HGFun` goals, native trust, per-test `maxHeartbeats`
caps at measured +5%).
