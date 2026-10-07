import Lynth.Interval.Core.Env
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Typed expression AST, denotation, evaluator, soundness

See `docs/interval/03-expr-registry.md §5`.
-/

namespace Lynth.Interval

/-! ### Custom n-ary functions -/

/-- argument/result types for custom functions (`rat` is exact `ℚ`,
evaluated through a side channel since `Ival` always rounds). -/
inductive CTy | nat | int | rat | real
deriving Repr, DecidableEq, Inhabited

namespace CTy

/-- the expression type carrying such values -/
@[reducible]
def toTy : CTy → Ty
  | .nat => .nat
  | .int => .int
  | .rat => .real
  | .real => .real

/-- exact semantic values -/
@[reducible]
def Val : CTy → Type
  | .nat => ℕ
  | .int => ℤ
  | .rat => ℚ
  | .real => ℝ

/-- enclosures (`rat` positions are exact-or-unknown) -/
@[reducible]
def Enc : CTy → Type
  | .nat => NIval
  | .int => ZIval
  | .rat => Option ℚ
  | .real => Ival

/-- enclosure correctness -/
@[reducible]
def EncOk : (t : CTy) → t.Enc → t.Val → Prop
  | .nat, X, v => Ty.Mem Ty.nat X v
  | .int, X, v => Ty.Mem Ty.int X v
  | .rat, o, v => ∀ q, o = some q → v = q
  | .real, X, v => Ty.Mem Ty.real X v

/-- asymptotic values (only `nat`/`real` carry information) -/
@[reducible]
def Asy : CTy → Type
  | .nat => NAsy
  | .int => Unit
  | .rat => Unit
  | .real => RAsy

instance : Lean.ToExpr CTy where
  toExpr
    | .nat => Lean.mkConst ``CTy.nat
    | .int => Lean.mkConst ``CTy.int
    | .rat => Lean.mkConst ``CTy.rat
    | .real => Lean.mkConst ``CTy.real
  toTypeExpr := Lean.mkConst ``CTy

end CTy

/-- heterogeneous value list -/
inductive CVal : List CTy → Type where
  | nil : CVal []
  | cons (t : CTy) {ts : List CTy} : t.Val → CVal ts → CVal (t :: ts)

/-- heterogeneous denotation list (what `Expr`s denote to) -/
inductive CDen : List CTy → Type where
  | nil : CDen []
  | cons (t : CTy) {ts : List CTy} : t.toTy.Val → CDen ts → CDen (t :: ts)

/-- heterogeneous enclosure list -/
inductive CEnc : List CTy → Type where
  | nil : CEnc []
  | cons (t : CTy) {ts : List CTy} : t.Enc → CEnc ts → CEnc (t :: ts)

/-- heterogeneous asymptotic list -/
inductive CAsy : List CTy → Type where
  | nil : CAsy []
  | cons (t : CTy) {ts : List CTy} : t.Asy → CAsy ts → CAsy (t :: ts)

/-- curried Lean function type over `tys` returning `r` -/
def curriedType : List CTy → CTy → Type
  | [], r => r.Val
  | t :: ts, r => t.Val → curriedType ts r

/-- apply a curried function to a value list -/
def applyCurried : (tys : List CTy) → (r : CTy) → curriedType tys r → CVal tys → r.Val
  | [], _ => fun f xs => match xs with | .nil => f
  | _ :: _, _ => fun f xs => match xs with | .cons _ v vs => applyCurried _ _ (f v) vs

/-- pointwise enclosure correctness -/
@[reducible]
def CEncHolds : {tys : List CTy} → CEnc tys → CDen tys → Prop
  | _, .nil, .nil => True
  | (.nat :: _), .cons .nat X Xs, .cons .nat d ds => Ty.Mem Ty.nat X d ∧ CEncHolds Xs ds
  | (.int :: _), .cons .int X Xs, .cons .int d ds => Ty.Mem Ty.int X d ∧ CEncHolds Xs ds
  | (.rat :: _), .cons .rat o Xs, .cons .rat d ds => (∀ q, o = some q → d = (q : ℝ)) ∧ CEncHolds Xs ds
  | (.real :: _), .cons .real X Xs, .cons .real d ds => Ty.Mem Ty.real X d ∧ CEncHolds Xs ds

/-- `ℚ` exact value as `ℝ` (helper avoids nested ascriptions) -/
def ratOut (q : ℚ) : ℝ := (q : ℝ)

/-- exact values agree with denotations -/
@[reducible]
def Agree : {tys : List CTy} → CVal tys → CDen tys → Prop
  | _, .nil, .nil => True
  | (.nat :: _), .cons .nat v vs, .cons .nat d ds => v = d ∧ Agree vs ds
  | (.int :: _), .cons .int v vs, .cons .int d ds => v = d ∧ Agree vs ds
  | (.rat :: _), .cons .rat v vs, .cons .rat d ds => d = ratOut v ∧ Agree vs ds
  | (.real :: _), .cons .real v vs, .cons .real d ds => v = d ∧ Agree vs ds

/-- cast an exact result value to its enclosure type -/
def castOut : (r : CTy) → CTy.Val r → r.toTy.Val
  | .nat, v => v
  | .int, v => v
  | .rat, q => ratOut q
  | .real, x => x

/-- n-ary custom function record.
`graph` is over exact values (`ℚ` for `rat`); `castOut` moves to the
enclosure type at the boundary. -/
structure CFn (tys : List CTy) (r : CTy) where
  name : String
  fn : curriedType tys r
  graph : CVal tys → CTy.Val r → Prop
  exu : ∀ xs, ∃! y, graph xs y
  ev : Ctx → CEnc tys → r.toTy.Enc
  sound : ∀ c (vs : CVal tys) (ds : CDen tys) (y' : CTy.Val r) (y : r.toTy.Val) X,
    c.Valid → graph vs y' → castOut r y' = y →
    CEncHolds X ds → Agree vs ds → r.toTy.Mem (ev c X) y
  cost : Nat := 1
  asy : Ctx → ℕ → CAsy tys → r.toTy.Asy := fun _ _ _ => r.toTy.asyTop
  asy_sound : ∀ (c : Ctx) (N : ℕ) (A : CAsy tys) (g : ℕ → r.toTy.Val),
    c.Valid → r.toTy.AsyHolds N g (asy c N A) := by
    intros; exact Ty.asyHolds_top _ _ _

namespace CFn

/-- the denoted (choice) function -/
noncomputable def fn' {tys : List CTy} {r : CTy} (f : CFn tys r)
    (xs : CVal tys) : CTy.Val r :=
  (f.exu xs).exists.choose

theorem fn_spec {tys : List CTy} {r : CTy} (f : CFn tys r)
    (xs : CVal tys) : f.graph xs (f.fn' xs) :=
  (f.exu xs).exists.choose_spec

theorem eq_fn {tys : List CTy} {r : CTy} (f : CFn tys r)
    {xs : CVal tys} {y' : CTy.Val r}
    (h : f.graph xs y') : y' = f.fn' xs :=
  (f.exu xs).unique h (f.fn_spec xs)

/-- graph from a curried function -/
def graphOf (tys : List CTy) (r : CTy) (F : curriedType tys r) :
    CVal tys → CTy.Val r → Prop :=
  fun xs y => y = applyCurried tys r F xs

/-- functionality is automatic for equation graphs -/
theorem exuOf {tys : List CTy} (r : CTy) (F : curriedType tys r) :
    ∀ xs, ∃! y, graphOf tys r F xs y := by
  intro xs
  exact ⟨_, rfl, fun _ h => h⟩

end CFn

-- Typed expressions over the open function registry (with `CArg`).
mutual
inductive Expr : Ty → Type where
  /-- exact rational constant -/
  | lit (q : ℚ) : Expr .real
  /-- natural number literal -/
  | natLit (n : ℕ) : Expr .nat
  /-- integer literal -/
  | intLit (z : ℤ) : Expr .int
  /-- de Bruijn variable of the given type -/
  | var (t : Ty) (i : ℕ) : Expr t
  | c0 {r : Ty} (f : Fn0 r) : Expr r
  | c1 {a r : Ty} (f : Fn1 a r) (x : Expr a) : Expr r
  | c2 {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) : Expr r
  /-- n-ary custom function call (explicit result index: `r.toTy` is not
      injective, so matching needs `ht` instead of solving for `r`) -/
  | call {tys : List CTy} {r : CTy} {t : Ty} (ht : t = r.toTy)
      (f : CFn tys r) (xs : CArg tys) : Expr t
  /-- rat-result call with inline exact runner (avoids `r`-dependent statements) -/
  | callRat {tys : List CTy} (f : CFn tys .rat) (xs : CArg tys)
      (qf : CVal tys → ℚ)
      (hcorr : ∀ xs (y' : CTy.Val .rat), f.graph xs y' → qf xs = y') : Expr .real
  /-- `∑ k ∈ Finset.range n, body`; `body` binds a `.nat` variable (index 0) -/
  | sum (t : Ty) (n : Expr .nat) (body : Expr t) : Expr t
/-- heterogeneous argument-expression list -/
inductive CArg : List CTy → Type where
  | nil : CArg []
  | cons (t : CTy) {ts : List CTy} : Expr t.toTy → CArg ts → CArg (t :: ts)
end

/-- exact values from denotations (choice for irrational rat denotations) -/
noncomputable def toVal : {tys : List CTy} → CDen tys → CVal tys
  | _, .nil => .nil
  | (.nat :: _), .cons .nat d ds => .cons .nat d (toVal ds)
  | (.int :: _), .cons .int d ds => .cons .int d (toVal ds)
  | (.rat :: _), .cons .rat d ds =>
    .cons .rat (@dite _ (∃ q : ℚ, d = ↑q) (Classical.propDecidable _) (fun h => h.choose) (fun _ => (0 : ℚ))) (toVal ds)
  | (.real :: _), .cons .real d ds => .cons .real d (toVal ds)

/-- unfolding equations (by `rfl`; avoids missing equational lemmas) -/
theorem toVal_nil : toVal CDen.nil = CVal.nil := rfl
theorem toVal_cons_nat' {ts : List CTy} (d : ℕ) (ds : CDen ts) :
    toVal (CDen.cons .nat d ds) = CVal.cons .nat d (toVal ds) := rfl
theorem toVal_cons_int' {ts : List CTy} (d : ℤ) (ds : CDen ts) :
    toVal (CDen.cons .int d ds) = CVal.cons .int d (toVal ds) := rfl
theorem toVal_cons_real' {ts : List CTy} (d : ℝ) (ds : CDen ts) :
    toVal (CDen.cons .real d ds) = CVal.cons .real d (toVal ds) := rfl
theorem toVal_cons_rat' {ts : List CTy} (d : ℝ) (ds : CDen ts) :
    toVal (CDen.cons .rat d ds)
      = CVal.cons .rat (@dite _ (∃ q : ℚ, d = ↑q) (Classical.propDecidable _) (fun h => h.choose) (fun _ => (0 : ℚ))) (toVal ds) := rfl

/-- agreement determines `toVal` -/
theorem toVal_agrees : ∀ {tys : List CTy} {vs : CVal tys} {ds : CDen tys},
    Agree vs ds → toVal ds = vs
  | _, .nil, .nil, _ => rfl
  | (.nat :: _), .cons .nat v vs, .cons .nat d ds, h => by
    have hvd := h.1; have hag := h.2
    subst hvd
    rw [toVal_cons_nat', toVal_agrees hag]
  | (.int :: _), .cons .int v vs, .cons .int d ds, h => by
    have hvd := h.1; have hag := h.2
    subst hvd
    rw [toVal_cons_int', toVal_agrees hag]
  | (.rat :: _), .cons .rat v vs, .cons .rat d ds, h => by
    have hdv := h.1; have hag := h.2
    have hex : ∃ q : ℚ, d = ↑q := ⟨v, hdv⟩
    haveI := Classical.propDecidable (∃ q : ℚ, d = ↑q)
    have hc : hex.choose = v := by
      have h2 : ((hex.choose : ℚ) : ℝ) = ((v : ℚ) : ℝ) := by
        rw [← hex.choose_spec]; exact hdv
      exact_mod_cast h2
    rw [toVal_cons_rat', toVal_agrees hag, dif_pos hex, hc]
  | (.real :: _), .cons .real v vs, .cons .real d ds, h => by
    have hvd := h.1; have hag := h.2
    subst hvd
    rw [toVal_cons_real', toVal_agrees hag]

/-- agreeing values coincide -/
theorem agreeUnique : ∀ {tys : List CTy} {vs vs' : CVal tys} {ds : CDen tys},
    Agree vs ds → Agree vs' ds → vs = vs'
  | _, .nil, .nil, _, _, _ => rfl
  | (.nat :: _), .cons .nat v vs, .cons .nat v' vs', .cons .nat d ds,
    hA, hB => by
    have h1 := hA.1; have h12 := hA.2; have h2 := hB.1; have h22 := hB.2
    subst h1; subst h2; rw [agreeUnique h12 h22]
  | (.int :: _), .cons .int v vs, .cons .int v' vs', .cons .int d ds,
    hA, hB => by
    have h1 := hA.1; have h12 := hA.2; have h2 := hB.1; have h22 := hB.2
    subst h1; subst h2; rw [agreeUnique h12 h22]
  | (.rat :: _), .cons .rat v vs, .cons .rat v' vs', .cons .rat d ds,
    hA, hB => by
    have h1 := hA.1; have h12 := hA.2; have h2 := hB.1; have h22 := hB.2
    have hv : v = v' := by
      have hcast : ratOut v = ratOut v' := by rw [← h1]; exact h2
      simp only [ratOut] at hcast
      exact_mod_cast hcast
    subst hv; rw [agreeUnique h12 h22]
  | (.real :: _), .cons .real v vs, .cons .real v' vs', .cons .real d ds,
    hA, hB => by
    have h1 := hA.1; have h12 := hA.2; have h2 := hB.1; have h22 := hB.2
    subst h1; subst h2; rw [agreeUnique h12 h22]

/-- resolve exact values from enclosures alone (real positions never resolve) -/
def resolveExact : {tys : List CTy} → CEnc tys → Option (CVal tys)
  | _, .nil => some .nil
  | (.nat :: _), .cons .nat X Xs =>
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (.cons .nat v vs)
    | _, _ => none
  | (.int :: _), .cons .int X Xs =>
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (.cons .int v vs)
    | _, _ => none
  | (.rat :: _), .cons .rat o Xs =>
    match o, resolveExact Xs with
    | some q, some vs => some (.cons .rat q vs)
    | _, _ => none
  | (.real :: _), .cons .real _ _ => none

/-- unfolding equations (by `rfl`) -/
theorem resolveExact_cons_nat {ts : List CTy} (X : NIval) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .nat X Xs) =
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (CVal.cons .nat v vs)
    | _, _ => none := rfl
theorem resolveExact_cons_int {ts : List CTy} (X : ZIval) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .int X Xs) =
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (CVal.cons .int v vs)
    | _, _ => none := rfl
theorem resolveExact_cons_rat {ts : List CTy} (o : Option ℚ) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .rat o Xs) =
    match o, resolveExact Xs with
    | some q, some vs => some (CVal.cons .rat q vs)
    | _, _ => none := rfl
theorem resolveExact_cons_real {ts : List CTy} (X : Ival) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .real X Xs) = none := rfl

/-- resolved values agree with denotations -/
theorem resolveExact_agrees : ∀ {tys : List CTy} {X : CEnc tys} {ds : CDen tys}
    {vs : CVal tys}, CEncHolds X ds → resolveExact X = some vs → Agree vs ds
  | _, .nil, .nil, .nil, _, _ => trivial
  | (.nat :: _), .cons .nat X Xs, .cons .nat d ds, .cons .nat v vs, h, he => by
    have hm := h.1; have hrest := h.2
    cases hX : X.isPoint with
    | some v' =>
      cases hXs : resolveExact Xs with
      | some vs' =>
        rw [resolveExact_cons_nat] at he
        simp only [hX, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveExact_agrees hrest hXs⟩
        exact (NIval.eq_of_isPoint hm hX).symm
      | none =>
        rw [resolveExact_cons_nat] at he
        simp only [hX, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveExact_cons_nat] at he
      simp only [hX] at he
      exact nomatch he
  | (.int :: _), .cons .int X Xs, .cons .int d ds, .cons .int v vs, h, he => by
    have hm := h.1; have hrest := h.2
    cases hX : X.isPoint with
    | some v' =>
      cases hXs : resolveExact Xs with
      | some vs' =>
        rw [resolveExact_cons_int] at he
        simp only [hX, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveExact_agrees hrest hXs⟩
        exact (ZIval.eq_of_isPoint hm hX).symm
      | none =>
        rw [resolveExact_cons_int] at he
        simp only [hX, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveExact_cons_int] at he
      simp only [hX] at he
      exact nomatch he
  | (.rat :: _), .cons .rat o Xs, .cons .rat d ds, .cons .rat v vs, h, he => by
    have hHolds : (∀ q : ℚ, o = some q → d = ratOut q) ∧ CEncHolds Xs ds := h
    obtain ⟨hm, hrest⟩ := hHolds
    cases hq : o with
    | some q =>
      cases hXs : resolveExact Xs with
      | some vs' =>
        rw [resolveExact_cons_rat] at he
        simp only [hq, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveExact_agrees hrest hXs⟩
        exact hm _ hq
      | none =>
        rw [resolveExact_cons_rat] at he
        simp only [hq, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveExact_cons_rat] at he
      simp only [hq] at he
      exact nomatch he
  | (.real :: _), .cons .real _ _, .cons .real _ _, _, _, he => by
    rw [resolveExact_cons_real] at he
    exact nomatch he

/-- auto evaluator into naturals -/
def CFn.evOfNat {tys : List CTy} (F : curriedType tys .nat)
    (c : Ctx) (X : CEnc tys) : NIval :=
  match resolveExact X with
  | some vs => NIval.pt (applyCurried tys .nat F vs)
  | none => NIval.top

theorem CFn.evOfNat_sound {tys : List CTy} (F : curriedType tys .nat)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y' : CTy.Val .nat) (y : Ty.Val .nat) X
    (hc : c.Valid)
    (hg : y' = applyCurried tys .nat F vs) (hout : castOut .nat y' = y)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    NIval.Mem (CFn.evOfNat F c X) y := by
  simp only [castOut] at hout
  subst hout; subst hg
  unfold CFn.evOfNat
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact NIval.mem_pt _
  | none => exact NIval.mem_top _

/-- auto evaluator into integers -/
def CFn.evOfInt {tys : List CTy} (F : curriedType tys .int)
    (c : Ctx) (X : CEnc tys) : ZIval :=
  match resolveExact X with
  | some vs => ZIval.pt (applyCurried tys .int F vs)
  | none => ZIval.top

theorem CFn.evOfInt_sound {tys : List CTy} (F : curriedType tys .int)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y' : CTy.Val .int) (y : Ty.Val .int) X
    (hc : c.Valid)
    (hg : y' = applyCurried tys .int F vs) (hout : castOut .int y' = y)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    ZIval.Mem (CFn.evOfInt F c X) y := by
  simp only [castOut] at hout
  subst hout; subst hg
  unfold CFn.evOfInt
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact ZIval.mem_pt _
  | none => exact ZIval.mem_top _

/-- auto evaluator into rationals (rounded enclosure, exact via `qrun`) -/
def CFn.evOfRat {tys : List CTy} (F : curriedType tys .rat)
    (c : Ctx) (X : CEnc tys) : Ival :=
  match resolveExact X with
  | some vs => Ival.ofRat c.prec (applyCurried tys .rat F vs)
  | none => Ival.top

theorem CFn.evOfRat_sound {tys : List CTy} (F : curriedType tys .rat)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y' : CTy.Val .rat) (y : Ty.Val .real) X
    (hc : c.Valid)
    (hg : y' = applyCurried tys .rat F vs) (hout : castOut .rat y' = y)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    Ival.Mem (CFn.evOfRat F c X) y := by
  simp only [castOut, ratOut] at hout
  subst hout; subst hg
  unfold CFn.evOfRat
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact Ival.mem_ofRat _ _
  | none => exact Ival.mem_top _

/-- auto-lift a curried function (discrete args; `real` positions always widen) -/
def CFn.ofFn (tys : List CTy) : (r : CTy) → curriedType tys r →
    String → Nat → CFn tys r
  | .nat, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys .nat F, exu := CFn.exuOf .nat F,
      ev := CFn.evOfNat F, sound := CFn.evOfNat_sound F, cost }
  | .int, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys .int F, exu := CFn.exuOf .int F,
      ev := CFn.evOfInt F, sound := CFn.evOfInt_sound F, cost }
  | .rat, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys .rat F, exu := CFn.exuOf .rat F,
      ev := CFn.evOfRat F, sound := CFn.evOfRat_sound F, cost }
  | .real, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys .real F, exu := CFn.exuOf .real F,
      ev := fun _ _ => Ival.top,
      sound := fun _ _ _ _ _ _ _ _ _ _ _ => Ival.mem_top _, cost }

/-- manual entry: user supplies evaluator + soundness against the auto graph -/
def CFn.manual (tys : List CTy) (r : CTy) (F : curriedType tys r)
    (ev : Ctx → CEnc tys → r.toTy.Enc)
    (sound : ∀ c (vs : CVal tys) (ds : CDen tys) (y' : CTy.Val r) (y : r.toTy.Val) X,
      c.Valid → CFn.graphOf tys r F vs y' → castOut r y' = y →
      CEncHolds X ds → Agree vs ds → r.toTy.Mem (ev c X) y)
    (name : String := "") (cost : Nat := 1) : CFn tys r :=
  { name, fn := F, graph := CFn.graphOf tys r F, exu := CFn.exuOf r F,
    ev, sound, cost }

namespace Expr

mutual
/-- Denotation. -/
noncomputable def denote : {t : Ty} → Expr t → SEnv → t.Val
  | _, .lit q, _ => (q : ℝ)
  | _, .natLit n, _ => n
  | _, .intLit z, _ => z
  | _, .var t i, ρ => ρ.get t i
  | _, .c0 f, _ => f.val
  | _, .c1 f x, ρ => f.fn (x.denote ρ)
  | _, .c2 f x y, ρ => f.fn (x.denote ρ) (y.denote ρ)
  | _, @Expr.call tys r t ht f xs, ρ => by
    subst ht
    exact castOut r (f.fn' (toVal (CArg.denoteArgs ρ xs)))
  | _, @Expr.callRat tys f xs qf _, ρ => ratOut (qf (toVal (CArg.denoteArgs ρ xs)))
  | _, .sum t n body, ρ => ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)

/-- denotations of an argument list -/
noncomputable def CArg.denoteArgs (ρ : SEnv) : {tys : List CTy} → CArg tys → CDen tys
  | _, .nil => .nil
  | _ :: _, .cons t e es => .cons t (e.denote ρ) (CArg.denoteArgs ρ es)
end

#check @CArg.denoteArgs
#check @Expr.denote

/-- `f lo + … + f (lo + n - 1)`, linear -/
def sumLin (t : Ty) (p : Nat) (f : Nat → t.Enc) (lo : Nat) : Nat → t.Enc
  | 0 => t.zeroE
  | n + 1 => t.addE p (sumLin t p f lo n) (f (lo + n))

/-- `f lo + … + f (lo + n - 1)`, balanced (kernel recursion depth `O(log n)`) -/
def sumBal (t : Ty) (p : Nat) (f : Nat → t.Enc) : Nat → Nat → Nat → t.Enc
  | 0, lo, n => sumLin t p f lo n
  | fuel + 1, lo, n =>
    if n ≤ 4 then sumLin t p f lo n
    else t.addE p (sumBal t p f fuel lo (n / 2)) (sumBal t p f fuel (lo + n / 2) (n - n / 2))

/-- `f 0 + … + f (N-1)` -/
def sumLoop (t : Ty) (p : Nat) (f : Nat → t.Enc) (N : Nat) : t.Enc := sumBal t p f 64 0 N

/-- resolve with denotations filling real positions -/
def resolveFull : {tys : List CTy} → CDen tys → CEnc tys → Option (CVal tys)
  | _, .nil, .nil => some .nil
  | (.nat :: _), .cons .nat d ds, .cons .nat X Xs =>
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (.cons .nat v vs)
    | _, _ => none
  | (.int :: _), .cons .int d ds, .cons .int X Xs =>
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (.cons .int v vs)
    | _, _ => none
  | (.rat :: _), .cons .rat d ds, .cons .rat o Xs =>
    match o, resolveFull ds Xs with
    | some q, some vs => some (.cons .rat q vs)
    | _, _ => none
  | (.real :: _), .cons .real d ds, .cons .real _ Xs =>
    match resolveFull ds Xs with
    | some vs => some (.cons .real d vs)
    | none => none

/-- unfolding equations (by `rfl`) -/
theorem resolveFull_cons_nat {ts : List CTy} (d : ℕ) (ds : CDen ts)
    (X : NIval) (Xs : CEnc ts) :
    resolveFull (CDen.cons .nat d ds) (CEnc.cons .nat X Xs) =
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (CVal.cons .nat v vs)
    | _, _ => none := rfl
theorem resolveFull_cons_int {ts : List CTy} (d : ℤ) (ds : CDen ts)
    (X : ZIval) (Xs : CEnc ts) :
    resolveFull (CDen.cons .int d ds) (CEnc.cons .int X Xs) =
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (CVal.cons .int v vs)
    | _, _ => none := rfl
theorem resolveFull_cons_rat {ts : List CTy} (d : ℝ) (ds : CDen ts)
    (o : Option ℚ) (Xs : CEnc ts) :
    resolveFull (CDen.cons .rat d ds) (CEnc.cons .rat o Xs) =
    match o, resolveFull ds Xs with
    | some q, some vs => some (CVal.cons .rat q vs)
    | _, _ => none := rfl
theorem resolveFull_cons_real {ts : List CTy} (d : ℝ) (ds : CDen ts)
    (X : Ival) (Xs : CEnc ts) :
    resolveFull (CDen.cons .real d ds) (CEnc.cons .real X Xs) =
    match resolveFull ds Xs with
    | some vs => some (CVal.cons .real d vs)
    | none => none := rfl

/-- resolved values agree with denotations -/
theorem resolveFull_sound : ∀ {tys : List CTy} {ds : CDen tys} {X : CEnc tys}
    {vs : CVal tys}, CEncHolds X ds → resolveFull ds X = some vs → Agree vs ds
  | _, .nil, .nil, .nil, _, _ => trivial
  | (.nat :: _), .cons .nat d ds, .cons .nat X Xs, .cons .nat v vs, h, he => by
    have hm := h.1; have hrest := h.2
    cases hX : X.isPoint with
    | some v' =>
      cases hXs : resolveFull ds Xs with
      | some vs' =>
        rw [resolveFull_cons_nat] at he
        simp only [hX, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveFull_sound hrest hXs⟩
        exact (NIval.eq_of_isPoint hm hX).symm
      | none =>
        rw [resolveFull_cons_nat] at he
        simp only [hX, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveFull_cons_nat] at he
      simp only [hX] at he
      exact nomatch he
  | (.int :: _), .cons .int d ds, .cons .int X Xs, .cons .int v vs, h, he => by
    have hm := h.1; have hrest := h.2
    cases hX : X.isPoint with
    | some v' =>
      cases hXs : resolveFull ds Xs with
      | some vs' =>
        rw [resolveFull_cons_int] at he
        simp only [hX, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveFull_sound hrest hXs⟩
        exact (ZIval.eq_of_isPoint hm hX).symm
      | none =>
        rw [resolveFull_cons_int] at he
        simp only [hX, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveFull_cons_int] at he
      simp only [hX] at he
      exact nomatch he
  | (.rat :: _), .cons .rat d ds, .cons .rat o Xs, .cons .rat v vs, h, he => by
    have hHolds : (∀ q : ℚ, o = some q → d = ratOut q) ∧ CEncHolds Xs ds := h
    obtain ⟨hm, hrest⟩ := hHolds
    cases hq : o with
    | some q =>
      cases hXs : resolveFull ds Xs with
      | some vs' =>
        rw [resolveFull_cons_rat] at he
        simp only [hq, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveFull_sound hrest hXs⟩
        exact hm _ hq
      | none =>
        rw [resolveFull_cons_rat] at he
        simp only [hq, hXs] at he
        exact nomatch he
    | none =>
      rw [resolveFull_cons_rat] at he
      simp only [hq] at he
      exact nomatch he
  | (.real :: _), .cons .real d ds, .cons .real _ Xs, .cons .real v vs, h, he => by
    have hrest := h.2
    cases hXs : resolveFull ds Xs with
    | some vs' =>
      rw [resolveFull_cons_real] at he
      simp only [hXs, Option.some_inj, CVal.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, resolveFull_sound hrest hXs⟩
    | none =>
      rw [resolveFull_cons_real] at he
      simp only [hXs] at he
      exact nomatch he

/-- all discrete positions resolved (real positions skipped) -/
def allDiscreteResolved : {tys : List CTy} → CEnc tys → Bool
  | _, .nil => true
  | (.nat :: _), .cons .nat X Xs => X.isPoint.isSome && allDiscreteResolved Xs
  | (.int :: _), .cons .int X Xs => X.isPoint.isSome && allDiscreteResolved Xs
  | (.rat :: _), .cons .rat o Xs => o.isSome && allDiscreteResolved Xs
  | (.real :: _), .cons .real _ Xs => allDiscreteResolved Xs

/-- the guard implies full resolution -/
theorem resolveFull_of_guard : ∀ {tys : List CTy} (ds : CDen tys) {X : CEnc tys},
    allDiscreteResolved X = true → ∃ vs, resolveFull ds X = some vs
  | _, .nil, .nil, _ => ⟨.nil, rfl⟩
  | (.nat :: _), .cons .nat d ds, .cons .nat X Xs, h => by
    simp only [allDiscreteResolved, Bool.and_eq_true] at h
    obtain ⟨hp, hrest⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds hrest
    exact ⟨.cons .nat v vs, by rw [resolveFull_cons_nat, hv, hvs]⟩
  | (.int :: _), .cons .int d ds, .cons .int X Xs, h => by
    simp only [allDiscreteResolved, Bool.and_eq_true] at h
    obtain ⟨hp, hrest⟩ := h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds hrest
    exact ⟨.cons .int v vs, by rw [resolveFull_cons_int, hv, hvs]⟩
  | (.rat :: _), .cons .rat d ds, .cons .rat o Xs, h => by
    simp only [allDiscreteResolved, Bool.and_eq_true] at h
    obtain ⟨hp, hrest⟩ := h
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds hrest
    exact ⟨.cons .rat q vs, by rw [resolveFull_cons_rat, hq, hvs]⟩
  | (.real :: _), .cons .real d ds, .cons .real _ Xs, h => by
    simp only [allDiscreteResolved] at h
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds h
    exact ⟨.cons .real d vs, by rw [resolveFull_cons_real, hvs]⟩

-- Interval evaluation (with argument-list and exact-rational evaluation).
mutual
def eval (c : Ctx) : {t : Ty} → Expr t → IEnv → t.Enc
  | _, .lit q, _ => Ival.ofRat c.prec q
  | _, .natLit n, _ => NIval.pt n
  | _, .intLit z, _ => ZIval.pt z
  | _, .var t i, σ => σ.get t i
  | _, .c0 f, _ => f.ev c
  | _, .c1 f x, σ => f.ev c (x.eval c σ)
  | _, .c2 f x y, σ => f.ev c (x.eval c σ) (y.eval c σ)
  | _, @Expr.call tys r t ht f xs, σ => by
    subst ht
    exact let X := evalCArgs c σ xs
      if allDiscreteResolved X then f.ev c X else r.toTy.top
  | _, @Expr.callRat tys f xs _ _, σ =>
    let X := evalCArgs c σ xs
    if allDiscreteResolved X then f.ev c X else Ival.top
  | _, .sum t n body, σ =>
    match NIval.isPoint (n.eval c σ) with
    | some N => sumLoop t c.prec (fun k => body.eval c (σ.push .nat (NIval.pt k))) N
    | none => t.top

/-- evaluate an argument list -/
def evalCArgs (c : Ctx) (σ : IEnv) : {tys : List CTy} → CArg tys → CEnc tys
  | _, .nil => .nil
  | (.nat :: _), .cons .nat e es => .cons .nat (e.eval c σ) (evalCArgs c σ es)
  | (.int :: _), .cons .int e es => .cons .int (e.eval c σ) (evalCArgs c σ es)
  | (.rat :: _), .cons .rat e es => .cons .rat (evalRat c σ e) (evalCArgs c σ es)
  | (.real :: _), .cons .real e es => .cons .real (e.eval c σ) (evalCArgs c σ es)

/-- exact-`ℚ` evaluation (literals and rat chains) -/
def evalRat (c : Ctx) (σ : IEnv) : Expr .real → Option ℚ
  | .lit q => some q
  | @Expr.callRat tys f xs qf _ =>
    (resolveExact (evalCArgs c σ xs)).map qf
  | _ => none
end

theorem sumLin_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) (lo : Nat) :
    ∀ n, t.Mem (sumLin t p F lo n) (∑ i ∈ Finset.range n, f (lo + i))
  | 0 => by simpa [sumLin] using t.mem_zeroE
  | n + 1 => by
    rw [Finset.sum_range_succ]
    exact t.mem_addE (sumLin_sound t p F f h lo n) (h _)

theorem sumBal_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) :
    ∀ fuel lo n, t.Mem (sumBal t p F fuel lo n) (∑ i ∈ Finset.range n, f (lo + i))
  | 0, lo, n => sumLin_sound t p F f h lo n
  | fuel + 1, lo, n => by
    unfold sumBal
    split
    · exact sumLin_sound t p F f h lo n
    · have e := Finset.sum_range_add (fun i => f (lo + i)) (n / 2) (n - n / 2)
      rw [show n / 2 + (n - n / 2) = n by omega] at e
      rw [e]
      refine t.mem_addE (sumBal_sound t p F f h fuel lo (n / 2)) ?_
      simpa [add_assoc] using sumBal_sound t p F f h fuel (lo + n / 2) (n - n / 2)

theorem sumLoop_sound (t : Ty) (p : Nat) (F : Nat → t.Enc) (f : ℕ → t.Val)
    (h : ∀ k, t.Mem (F k) (f k)) (N : Nat) : t.Mem (sumLoop t p F N) (∑ k ∈ Finset.range N, f k) := by
  unfold sumLoop; simpa using sumBal_sound t p F f h 64 0 N

-- **Soundness** of interval evaluation (with argument-list and exact-rational soundness).
mutual
theorem eval_sound {c : Ctx} (hc : c.Valid) :
    ∀ {t : Ty} (e : Expr t) {ρ : SEnv} {σ : IEnv}, σ.Holds ρ → t.Mem (e.eval c σ) (e.denote ρ)
  | _, .lit q, _, _, _ => by
    simp only [eval, denote, Ty.Mem]
    exact Ival.mem_ofRat _ _
  | _, .natLit n, _, _, _ => by
    simp only [eval, denote, Ty.Mem]
    exact NIval.mem_pt n
  | _, .intLit z, _, _, _ => by
    simp only [eval, denote, Ty.Mem]
    exact ZIval.mem_pt z
  | _, .var t i, _, _, h => by
    simp only [eval, denote, Ty.Mem]
    exact h t i
  | _, .c0 f, _, _, _ => by
    simp only [eval, denote, Ty.Mem]
    exact f.sound c _ hc f.val_spec
  | _, .c1 f x, _, _, h => by
    simp only [eval, denote, Ty.Mem]
    exact f.sound c _ _ _ hc (f.fn_spec _) (eval_sound hc x h)
  | _, .c2 f x y, _, _, h => by
    simp only [eval, denote, Ty.Mem]
    exact f.sound c _ _ _ _ _ hc (f.fn_spec _ _) (eval_sound hc x h) (eval_sound hc y h)
  | _, .sum t n body, ρ, σ, h => by
    simp only [eval, denote]
    show t.Mem (match NIval.isPoint (n.eval c σ) with
      | some N => sumLoop t c.prec (fun k => body.eval c (σ.push .nat (NIval.pt k))) N
      | none => t.top) (∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k))
    split
    · rename_i N hN
      have hn : n.denote ρ = N := NIval.eq_of_isPoint (eval_sound hc n h) hN
      rw [hn]
      exact sumLoop_sound t c.prec _ _
        (fun k => eval_sound hc body (h.push (t := .nat) (NIval.mem_pt k))) N
    · exact t.mem_top _
  | _, @Expr.call tys .nat t ht f xs, ρ, σ, h =>
    eval_sound_call hc ht f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .int t ht f xs, ρ, σ, h =>
    eval_sound_call hc ht f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .rat t ht f xs, ρ, σ, h =>
    eval_sound_call hc ht f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .real t ht f xs, ρ, σ, h =>
    eval_sound_call hc ht f xs (evalCArgs_sound hc h xs)
  | _, @Expr.callRat tys f xs qf hcorr, ρ, σ, h =>
    eval_sound_callRat hc f xs qf hcorr (evalCArgs_sound hc h xs)
theorem evalCArgs_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    (hs : σ.Holds ρ) : ∀ {tys : List CTy} (xs : CArg tys),
    CEncHolds (evalCArgs c σ xs) (CArg.denoteArgs ρ xs)
  | _, .nil => by simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
  | (.nat :: _), .cons .nat e es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    exact ⟨eval_sound hc e hs, evalCArgs_sound hc hs es⟩
  | (.int :: _), .cons .int e es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    exact ⟨eval_sound hc e hs, evalCArgs_sound hc hs es⟩
  | (.rat :: _), .cons .rat (.lit q') es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    obtain rfl := Option.some_inj.mp he
    rfl
  | (.rat :: _), .cons .rat (.var .real i) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.rat :: _), .cons .rat (.c0 f) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.rat :: _), .cons .rat (.c1 f x) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.rat :: _), .cons .rat (.c2 f x y) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.rat :: _), .cons .rat (@Expr.call tys r .real ht f xs) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.rat :: _), .cons .rat (@Expr.callRat tys f xs qf hcorr) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    cases hres : resolveExact (evalCArgs c σ xs) with
    | some vs =>
      simp only [hres, Option.map_some] at he
      have heq := Option.some_inj.mp he
      have hH := evalCArgs_sound hc hs xs
      have hag := resolveExact_agrees hH hres
      simp only [denote]
      show ratOut (qf (toVal (CArg.denoteArgs ρ xs))) = _
      rw [toVal_agrees hag, heq]
      rfl
    | none =>
      simp only [hres, Option.map_none] at he
      exact nomatch he
  | (.rat :: _), .cons .rat (.sum .real n body) es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    refine ⟨?_, evalCArgs_sound hc hs es⟩
    intro q he
    simp only [evalRat] at he
    exact nomatch he
  | (.real :: _), .cons .real e es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    exact ⟨eval_sound hc e hs, evalCArgs_sound hc hs es⟩
theorem eval_sound_call {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    {tys : List CTy} {r : CTy} {t : Ty} (ht : t = r.toTy)
    (f : CFn tys r) (xs : CArg tys)
    (hH : CEncHolds (evalCArgs c σ xs) (CArg.denoteArgs ρ xs)) :
    t.Mem ((Expr.call ht f xs).eval c σ) ((Expr.call ht f xs).denote ρ) := by
  subst ht
  simp only [eval, denote]
  split
  · rename_i hres
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard (CArg.denoteArgs ρ xs) hres
    have hag := resolveFull_sound hH hvs
    have htv := toVal_agrees hag
    have hg : f.graph vs (f.fn' vs) := f.fn_spec vs
    have hout : castOut r (f.fn' vs)
        = castOut r (f.fn' (toVal (CArg.denoteArgs ρ xs))) := by rw [htv]
    exact f.sound c vs _ _ _ _ hc hg hout hH hag
  · exact r.toTy.mem_top _

theorem eval_sound_callRat {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    {tys : List CTy} (f : CFn tys .rat) (xs : CArg tys)
    (qf : CVal tys → ℚ)
    (hcorr : ∀ xs (y' : CTy.Val .rat), f.graph xs y' → qf xs = y')
    (hH : CEncHolds (evalCArgs c σ xs) (CArg.denoteArgs ρ xs)) :
    Ty.Mem Ty.real ((Expr.callRat f xs qf hcorr).eval c σ)
      ((Expr.callRat f xs qf hcorr).denote ρ) := by
  simp only [eval, denote]
  split
  · rename_i hres
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard (CArg.denoteArgs ρ xs) hres
    have hag := resolveFull_sound hH hvs
    have htv := toVal_agrees hag
    rw [htv]
    have hg : f.graph vs (f.fn' vs) := f.fn_spec vs
    have hout : castOut .rat (f.fn' vs) = ratOut (qf vs) := by
      show ratOut (f.fn' vs) = _
      exact congrArg _ (hcorr _ _ (f.fn_spec vs)).symm
    exact f.sound c vs _ _ _ _ hc hg hout hH hag
  · exact Ival.mem_top _
end

theorem evalRat_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    (hs : σ.Holds ρ) : ∀ {e : Expr .real} {q : ℚ},
    evalRat c σ e = some q → e.denote ρ = (q : ℝ) := by
  intro e q he
  unfold evalRat at he
  split at he
  · obtain rfl := Option.some_inj.mp he
    rfl
  · rename_i tys f xs qf hcorr
    have he2 : (resolveExact (evalCArgs c σ xs)).map qf = some q := he
    cases hres : resolveExact (evalCArgs c σ xs) with
    | some vs =>
      simp only [hres, Option.map_some] at he2
      have heq := Option.some_inj.mp he2
      have hH := evalCArgs_sound hc hs xs
      have hag := resolveExact_agrees hH hres
      simp only [denote]
      show ratOut (qf (toVal (CArg.denoteArgs ρ xs))) = _
      rw [toVal_agrees hag, heq]
      rfl
    | none =>
      simp only [hres, Option.map_none] at he2
      exact nomatch he2
  · exact nomatch he

theorem call_eq {tys : List CTy} {r : CTy} {t : Ty} (ht : t = r.toTy)
    (f : CFn tys r) (xs : CArg tys) (ρ : SEnv)
    {vs : CVal tys} {ds : CDen tys} {y' : CTy.Val r} {Y : t.Val}
    (hds : ds = CArg.denoteArgs ρ xs) (hag : Agree vs ds)
    (hg : f.graph vs y') (hout : ht.symm ▸ castOut r y' = Y) :
    Y = (Expr.call ht f xs).denote ρ := by
  subst ht
  dsimp only at hout
  simp only [denote]
  show Y = castOut r (f.fn' (toVal (CArg.denoteArgs ρ xs)))
  rw [← hds, toVal_agrees hag]
  exact hout.symm.trans (congrArg _ (f.eq_fn hg))

theorem callRat_denote {tys : List CTy} (f : CFn tys .rat) (xs : CArg tys) (ρ : SEnv)
    {vs : CVal tys} {ds : CDen tys} {qf : CVal tys → ℚ}
    {hcorr : ∀ xs (y' : CTy.Val .rat), f.graph xs y' → qf xs = y'}
    (hds : ds = CArg.denoteArgs ρ xs) (hag : Agree vs ds) :
    (Expr.callRat f xs qf hcorr).denote ρ = ratOut (qf vs) := by
  simp only [denote]
  show ratOut (qf (toVal (CArg.denoteArgs ρ xs))) = _
  rw [← hds, toVal_agrees hag]

/-! ### Reification lemmas (used to build `orig = e.denote ρ` proofs) -/

theorem c0_eq {r : Ty} (f : Fn0 r) (ρ : SEnv) {Y : r.Val} (hY : f.graph Y) :
    Y = (Expr.c0 f).denote ρ := f.eq_val hY

theorem c1_eq {a r : Ty} (f : Fn1 a r) (x : Expr a) (ρ : SEnv) {X : a.Val} {Y : r.Val}
    (hX : X = x.denote ρ) (hY : f.graph X Y) : Y = (Expr.c1 f x).denote ρ := by
  subst hX; exact f.eq_fn hY

theorem c2_eq {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) (ρ : SEnv)
    {X : a.Val} {Y : b.Val} {Z : r.Val}
    (hX : X = x.denote ρ) (hY : Y = y.denote ρ) (hZ : f.graph X Y Z) :
    Z = (Expr.c2 f x y).denote ρ := by
  subst hX; subst hY; exact f.eq_fn hZ

theorem lit_eq (q : ℚ) (ρ : SEnv) {X : ℝ} (h : X = (q : ℝ)) : X = (Expr.lit q).denote ρ := h

theorem natLit_eq (n : ℕ) (ρ : SEnv) {X : ℕ} (h : X = n) : X = (Expr.natLit n).denote ρ := h

theorem intLit_eq (z : ℤ) (ρ : SEnv) {X : ℤ} (h : X = z) : X = (Expr.intLit z).denote ρ := h

theorem sum_eq (t : Ty) (n : Expr .nat) (body : Expr t) (ρ : SEnv) {N : ℕ} {f : ℕ → t.Val}
    (hN : N = n.denote ρ) (hf : ∀ k, f k = body.denote (ρ.push .nat k)) :
    ∑ k ∈ Finset.range N, f k = (Expr.sum t n body).denote ρ := by
  subst hN
  show _ = ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)
  exact Finset.sum_congr rfl (fun k _ => hf k)

end Expr

end Lynth.Interval
