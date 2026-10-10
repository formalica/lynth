import Lynth.Interval.Core.Env
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Typed expression AST, denotation, evaluator, soundness

See `docs/interval/03-expr-registry.md §5`.
-/

namespace Lynth.Interval

/-! ### Custom n-ary functions over unified `Ty`.

Positions are typed by `Ty` directly (there is no separate `CTy`): `.rat`
positions carry exact values (`Option ℚ`, unresolved is `none`) and are
reified from closed rational terms; `.list t` positions carry pointwise
enclosures (`none` is the trivial enclosure). -/

/-- heterogeneous value list -/
inductive CVal : List Ty → Type where
  | nil : CVal []
  | cons (t : Ty) {ts : List Ty} : t.Val → CVal ts → CVal (t :: ts)

/-- heterogeneous denotation list (what `Expr`s denote to) -/
inductive CDen : List Ty → Type where
  | nil : CDen []
  | cons (t : Ty) {ts : List Ty} : t.Val → CDen ts → CDen (t :: ts)

/-- heterogeneous enclosure list -/
inductive CEnc : List Ty → Type where
  | nil : CEnc []
  | cons (t : Ty) {ts : List Ty} : t.Enc → CEnc ts → CEnc (t :: ts)

/-- heterogeneous asymptotic list -/
inductive CAsy : List Ty → Type where
  | nil : CAsy []
  | cons (t : Ty) {ts : List Ty} : t.Asy → CAsy ts → CAsy (t :: ts)

/-- curried Lean function type over `tys` returning `r` -/
def curriedType : List Ty → Ty → Type
  | [], r => r.Val
  | t :: ts, r => t.Val → curriedType ts r

/-- apply a curried function to a value list -/
def applyCurried : (tys : List Ty) → (r : Ty) → curriedType tys r → CVal tys → r.Val
  | [], _ => fun f xs => match xs with | .nil => f
  | _ :: _, _ => fun f xs => match xs with | .cons _ v vs => applyCurried _ _ (f v) vs

/-- pointwise enclosure correctness -/
@[reducible]
def CEncHolds : {tys : List Ty} → CEnc tys → CDen tys → Prop
  | _, .nil, .nil => True
  | _, .cons t X Xs, .cons _ d ds => Ty.Mem t X d ∧ CEncHolds Xs ds

/-- exact values agree with denotations -/
@[reducible]
def Agree : {tys : List Ty} → CVal tys → CDen tys → Prop
  | _, .nil, .nil => True
  | (_ :: _), .cons _ v vs, .cons _ d ds => v = d ∧ Agree vs ds

/-- n-ary custom function record. `graph` is over exact values; `ev`
evaluates enclosures; `sound` connects them. -/
structure CFn (tys : List Ty) (r : Ty) where
  name : String
  fn : curriedType tys r
  graph : CVal tys → r.Val → Prop
  exu : ∀ xs, ∃! y, graph xs y
  ev : Ctx → CEnc tys → r.Enc
  sound : ∀ c (vs : CVal tys) (ds : CDen tys) (y : r.Val) X,
    c.Valid → graph vs y →
    CEncHolds X ds → Agree vs ds → r.Mem (ev c X) y
  cost : Nat := 1
  asy : Ctx → ℕ → CAsy tys → r.Asy := fun _ _ _ => r.asyTop
  asy_sound : ∀ (c : Ctx) (N : ℕ) (A : CAsy tys) (g : ℕ → r.Val),
    c.Valid → r.AsyHolds N g (asy c N A) := by
    intros; exact Ty.asyHolds_top _ _ _

namespace CFn

/-- the denoted (choice) function -/
noncomputable def fn' {tys : List Ty} {r : Ty} (f : CFn tys r)
    (xs : CVal tys) : r.Val :=
  (f.exu xs).exists.choose

theorem fn_spec {tys : List Ty} {r : Ty} (f : CFn tys r)
    (xs : CVal tys) : f.graph xs (f.fn' xs) :=
  (f.exu xs).exists.choose_spec

theorem eq_fn {tys : List Ty} {r : Ty} (f : CFn tys r)
    {xs : CVal tys} {y : r.Val}
    (h : f.graph xs y) : y = f.fn' xs :=
  (f.exu xs).unique h (f.fn_spec xs)

/-- graph from a curried function -/
def graphOf (tys : List Ty) (r : Ty) (F : curriedType tys r) :
    CVal tys → r.Val → Prop :=
  fun xs y => y = applyCurried tys r F xs

/-- functionality is automatic for equation graphs -/
theorem exuOf {tys : List Ty} (r : Ty) (F : curriedType tys r) :
    ∀ xs, ∃! y, graphOf tys r F xs y := by
  intro xs
  exact ⟨_, rfl, fun _ h => h⟩

end CFn

-- Typed expressions over the open function registry (with `CArg`).
mutual
inductive Expr : Ty → Type where
  /-- exact rational constant -/
  | lit (q : ℚ) : Expr .real
  /-- exact rational (for `.rat` positions) -/
  | rlit (q : ℚ) : Expr .rat
  /-- natural number literal -/
  | natLit (n : ℕ) : Expr .nat
  /-- integer literal -/
  | intLit (z : ℤ) : Expr .int
  /-- list literal (elementwise) -/
  | clist {t : Ty} (xs : ExprList t) : Expr (.list t)
  /-- de Bruijn variable of the given type -/
  | var (t : Ty) (i : ℕ) : Expr t
  | c0 {r : Ty} (f : Fn0 r) : Expr r
  | c1 {a r : Ty} (f : Fn1 a r) (x : Expr a) : Expr r
  | c2 {a b r : Ty} (f : Fn2 a b r) (x : Expr a) (y : Expr b) : Expr r
  /-- n-ary custom function call -/
  | call {tys : List Ty} {r : Ty} (f : CFn tys r) (xs : CArg tys) : Expr r
  /-- `∑ k ∈ Finset.range n, body`; `body` binds a `.nat` variable (index 0) -/
  | sum (t : Ty) (n : Expr .nat) (body : Expr t) : Expr t
/-- heterogeneous argument-expression list -/
inductive CArg : List Ty → Type where
  | nil : CArg []
  | cons (t : Ty) {ts : List Ty} : Expr t → CArg ts → CArg (t :: ts)
/-- heterogeneous expression list (list literals) -/
inductive ExprList : Ty → Type where
  | nil {t : Ty} : ExprList t
  | cons {t : Ty} (x : Expr t) (xs : ExprList t) : ExprList t
end

/-- exact values from denotations -/
noncomputable def toVal : {tys : List Ty} → CDen tys → CVal tys
  | _, .nil => .nil
  | (_ :: _), .cons _ d ds => .cons _ d (toVal ds)

/-- agreement determines `toVal` -/
theorem toVal_agrees : ∀ {tys : List Ty} {vs : CVal tys} {ds : CDen tys},
    Agree vs ds → toVal ds = vs
  | _, .nil, .nil, _ => rfl
  | (t :: _), .cons _ v vs, .cons _ d ds, h => by
    have hvd := h.1; have hag := h.2
    subst hvd
    exact congrArg (CVal.cons t _) (toVal_agrees hag)

/-- agreeing values coincide -/
theorem agreeUnique : ∀ {tys : List Ty} {vs vs' : CVal tys} {ds : CDen tys},
    Agree vs ds → Agree vs' ds → vs = vs'
  | _, .nil, .nil, _, _, _ => rfl
  | (t :: _), .cons _ v vs, .cons _ v' vs', .cons _ d ds, hA, hB => by
    have h1 := hA.1; have h12 := hA.2; have h2 := hB.1; have h22 := hB.2
    subst h1; subst h2
    exact congrArg (CVal.cons t _) (agreeUnique h12 h22)

/-- resolve exact values from enclosures alone (real positions never resolve) -/
def resolveExact : {tys : List Ty} → CEnc tys → Option (CVal tys)
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
  | (.cplx :: _), .cons .cplx _ _ => none
  | (.list _ :: _), .cons _ _ _ => none

/-- unfolding equations (by `rfl`) -/
theorem resolveExact_cons_nat {ts : List Ty} (X : NIval) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .nat X Xs) =
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (CVal.cons .nat v vs)
    | _, _ => none := rfl
theorem resolveExact_cons_int {ts : List Ty} (X : ZIval) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .int X Xs) =
    match X.isPoint, resolveExact Xs with
    | some v, some vs => some (CVal.cons .int v vs)
    | _, _ => none := rfl
theorem resolveExact_cons_rat {ts : List Ty} (o : Option ℚ) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .rat o Xs) =
    match o, resolveExact Xs with
    | some q, some vs => some (CVal.cons .rat q vs)
    | _, _ => none := rfl
theorem resolveExact_cons_real {ts : List Ty} (X : Ival) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .real X Xs) = none := rfl
theorem resolveExact_cons_cplx {ts : List Ty} (X : CBox) (Xs : CEnc ts) :
    resolveExact (CEnc.cons .cplx X Xs) = none := rfl
theorem resolveExact_cons_list {t : Ty} {ts : List Ty}
    (X : (Ty.list t).Enc) (Xs : CEnc ts) :
    resolveExact (CEnc.cons (Ty.list t) X Xs) = none := rfl

/-- resolved values agree with denotations -/
theorem resolveExact_agrees : ∀ {tys : List Ty} {X : CEnc tys} {ds : CDen tys}
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
    have hHolds : (∀ q : ℚ, o = some q → d = q) ∧ CEncHolds Xs ds := h
    obtain ⟨hm, hrest⟩ := hHolds
    cases hq : o with
    | some q =>
      cases hXs : resolveExact Xs with
      | some vs' =>
        rw [resolveExact_cons_rat] at he
        simp only [hq, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveExact_agrees hrest hXs⟩
        exact (hm _ hq).symm
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
  | (.cplx :: _), .cons .cplx _ _, .cons .cplx _ _, _, _, he => by
    rw [resolveExact_cons_cplx] at he
    exact nomatch he
  | (.list _ :: _), .cons _ _ _, .cons _ _ _, _, _, he => by
    rw [resolveExact_cons_list] at he
    exact nomatch he

/-- auto evaluator into naturals -/
def CFn.evOfNat {tys : List Ty} (F : curriedType tys .nat)
    (c : Ctx) (X : CEnc tys) : NIval :=
  match resolveExact X with
  | some vs => NIval.pt (applyCurried tys .nat F vs)
  | none => NIval.top

theorem CFn.evOfNat_sound {tys : List Ty} (F : curriedType tys .nat)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y : ℕ) X
    (hc : c.Valid)
    (hg : y = applyCurried tys .nat F vs)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    NIval.Mem (CFn.evOfNat F c X) y := by
  subst hg
  unfold CFn.evOfNat
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact NIval.mem_pt _
  | none => exact NIval.mem_top _

/-- auto evaluator into integers -/
def CFn.evOfInt {tys : List Ty} (F : curriedType tys .int)
    (c : Ctx) (X : CEnc tys) : ZIval :=
  match resolveExact X with
  | some vs => ZIval.pt (applyCurried tys .int F vs)
  | none => ZIval.top

theorem CFn.evOfInt_sound {tys : List Ty} (F : curriedType tys .int)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y : ℤ) X
    (hc : c.Valid)
    (hg : y = applyCurried tys .int F vs)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    ZIval.Mem (CFn.evOfInt F c X) y := by
  subst hg
  unfold CFn.evOfInt
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact ZIval.mem_pt _
  | none => exact ZIval.mem_top _

/-- auto evaluator into exact rationals -/
def CFn.evOfRat {tys : List Ty} (F : curriedType tys .rat)
    (c : Ctx) (X : CEnc tys) : Option ℚ :=
  match resolveExact X with
  | some vs => some (applyCurried tys .rat F vs)
  | none => none

theorem CFn.evOfRat_sound {tys : List Ty} (F : curriedType tys .rat)
    (c : Ctx) (vs : CVal tys) (ds : CDen tys) (y : ℚ) X
    (hc : c.Valid)
    (hg : y = applyCurried tys .rat F vs)
    (hh : CEncHolds X ds) (hag : Agree vs ds) :
    Ty.Mem .rat (CFn.evOfRat F c X) y := by
  subst hg
  unfold CFn.evOfRat
  match he : resolveExact X with
  | some vs' =>
    have hag' := resolveExact_agrees hh he
    have hvv : vs' = vs := agreeUnique hag' hag
    subst hvv
    exact fun _ h => Option.some_inj.mp h
  | none => exact fun _ h => nomatch h

/-- auto-lift a curried function (discrete args; other results widen to `⊤`) -/
def CFn.ofFn (tys : List Ty) : (r : Ty) → curriedType tys r →
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
      sound := fun _ _ _ _ _ _ _ _ _ => Ival.mem_top _, cost }
  | .cplx, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys .cplx F, exu := CFn.exuOf .cplx F,
      ev := fun _ _ => CBox.top,
      sound := fun _ _ _ _ _ _ _ _ _ => CBox.mem_top _, cost }
  | .list _, F, name, cost =>
    { name, fn := F, graph := CFn.graphOf tys _ F, exu := CFn.exuOf _ F,
      ev := fun _ _ => none,
      sound := fun _ _ _ _ _ _ _ _ _ => trivial, cost }

/-- manual entry: user supplies evaluator + soundness against the auto graph -/
def CFn.manual (tys : List Ty) (r : Ty) (F : curriedType tys r)
    (ev : Ctx → CEnc tys → r.Enc)
    (sound : ∀ c (vs : CVal tys) (ds : CDen tys) (y : r.Val) X,
      c.Valid → CFn.graphOf tys r F vs y →
      CEncHolds X ds → Agree vs ds → r.Mem (ev c X) y)
    (name : String := "") (cost : Nat := 1) : CFn tys r :=
  { name, fn := F, graph := CFn.graphOf tys r F, exu := CFn.exuOf r F,
    ev, sound, cost }

namespace Expr

mutual
/-- Denotation. -/
noncomputable def denote : {t : Ty} → Expr t → SEnv → t.Val
  | _, .lit q, _ => (q : ℝ)
  | _, .rlit q, _ => q
  | _, .natLit n, _ => n
  | _, .intLit z, _ => z
  | _, .clist xs, ρ => denoteList xs ρ
  | _, .var t i, ρ => ρ.get t i
  | _, .c0 f, _ => f.val
  | _, .c1 f x, ρ => f.fn (x.denote ρ)
  | _, .c2 f x y, ρ => f.fn (x.denote ρ) (y.denote ρ)
  | _, @Expr.call tys r f xs, ρ => f.fn' (toVal (CArg.denoteArgs ρ xs))
  | _, .sum t n body, ρ => ∑ k ∈ Finset.range (n.denote ρ), body.denote (ρ.push .nat k)

/-- denotations of an argument list -/
noncomputable def CArg.denoteArgs (ρ : SEnv) : {tys : List Ty} → CArg tys → CDen tys
  | _, .nil => .nil
  | _ :: _, .cons t e es => .cons t (e.denote ρ) (CArg.denoteArgs ρ es)

/-- denotations of a list literal -/
noncomputable def denoteList : {t : Ty} → ExprList t → SEnv → List t.Val
  | _, .nil, _ => []
  | _, .cons x xs, ρ => x.denote ρ :: denoteList xs ρ
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
def resolveFull : {tys : List Ty} → CDen tys → CEnc tys → Option (CVal tys)
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
  | (.cplx :: _), .cons .cplx d ds, .cons .cplx _ Xs =>
    match resolveFull ds Xs with
    | some vs => some (.cons .cplx d vs)
    | none => none
  | (.list _ :: _), .cons _ d ds, .cons _ _ Xs =>
    match resolveFull ds Xs with
    | some vs => some (.cons _ d vs)
    | none => none

/-- unfolding equations (by `rfl`) -/
theorem resolveFull_cons_nat {ts : List Ty} (d : ℕ) (ds : CDen ts)
    (X : NIval) (Xs : CEnc ts) :
    resolveFull (CDen.cons .nat d ds) (CEnc.cons .nat X Xs) =
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (CVal.cons .nat v vs)
    | _, _ => none := rfl
theorem resolveFull_cons_int {ts : List Ty} (d : ℤ) (ds : CDen ts)
    (X : ZIval) (Xs : CEnc ts) :
    resolveFull (CDen.cons .int d ds) (CEnc.cons .int X Xs) =
    match X.isPoint, resolveFull ds Xs with
    | some v, some vs => some (CVal.cons .int v vs)
    | _, _ => none := rfl
theorem resolveFull_cons_rat {ts : List Ty} (d : ℚ) (ds : CDen ts)
    (o : Option ℚ) (Xs : CEnc ts) :
    resolveFull (CDen.cons .rat d ds) (CEnc.cons .rat o Xs) =
    match o, resolveFull ds Xs with
    | some q, some vs => some (CVal.cons .rat q vs)
    | _, _ => none := rfl
theorem resolveFull_cons_real {ts : List Ty} (d : ℝ) (ds : CDen ts)
    (X : Ival) (Xs : CEnc ts) :
    resolveFull (CDen.cons .real d ds) (CEnc.cons .real X Xs) =
    match resolveFull ds Xs with
    | some vs => some (CVal.cons .real d vs)
    | none => none := rfl
theorem resolveFull_cons_cplx {ts : List Ty} (d : ℂ) (ds : CDen ts)
    (X : CBox) (Xs : CEnc ts) :
    resolveFull (CDen.cons .cplx d ds) (CEnc.cons .cplx X Xs) =
    match resolveFull ds Xs with
    | some vs => some (CVal.cons .cplx d vs)
    | none => none := rfl
theorem resolveFull_cons_list {t : Ty} {ts : List Ty} (d : List t.Val) (ds : CDen ts)
    (X : (Ty.list t).Enc) (Xs : CEnc ts) :
    resolveFull (CDen.cons (Ty.list t) d ds) (CEnc.cons (Ty.list t) X Xs) =
    match resolveFull ds Xs with
    | some vs => some (CVal.cons (Ty.list t) d vs)
    | none => none := rfl

/-- resolved values agree with denotations -/
theorem resolveFull_sound : ∀ {tys : List Ty} {ds : CDen tys} {X : CEnc tys}
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
    have hHolds : (∀ q : ℚ, o = some q → d = q) ∧ CEncHolds Xs ds := h
    obtain ⟨hm, hrest⟩ := hHolds
    cases hq : o with
    | some q =>
      cases hXs : resolveFull ds Xs with
      | some vs' =>
        rw [resolveFull_cons_rat] at he
        simp only [hq, hXs, Option.some_inj, CVal.cons.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        refine ⟨?_, resolveFull_sound hrest hXs⟩
        exact (hm _ hq).symm
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
  | (.cplx :: _), .cons .cplx d ds, .cons .cplx _ Xs, .cons .cplx v vs, h, he => by
    have hrest := h.2
    cases hXs : resolveFull ds Xs with
    | some vs' =>
      rw [resolveFull_cons_cplx] at he
      simp only [hXs, Option.some_inj, CVal.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, resolveFull_sound hrest hXs⟩
    | none =>
      rw [resolveFull_cons_cplx] at he
      simp only [hXs] at he
      exact nomatch he
  | (.list _ :: _), .cons _ d ds, .cons _ _ Xs, .cons _ v vs, h, he => by
    have hrest := h.2
    cases hXs : resolveFull ds Xs with
    | some vs' =>
      rw [resolveFull_cons_list] at he
      simp only [hXs, Option.some_inj, CVal.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact ⟨rfl, resolveFull_sound hrest hXs⟩
    | none =>
      rw [resolveFull_cons_list] at he
      simp only [hXs] at he
      exact nomatch he

/-- all discrete positions resolved (other positions skipped) -/
def allDiscreteResolved : {tys : List Ty} → CEnc tys → Bool
  | _, .nil => true
  | (.nat :: _), .cons .nat X Xs => X.isPoint.isSome && allDiscreteResolved Xs
  | (.int :: _), .cons .int X Xs => X.isPoint.isSome && allDiscreteResolved Xs
  | (.rat :: _), .cons .rat o Xs => o.isSome && allDiscreteResolved Xs
  | (.real :: _), .cons .real _ Xs => allDiscreteResolved Xs
  | (.cplx :: _), .cons .cplx _ Xs => allDiscreteResolved Xs
  | (.list _ :: _), .cons _ _ Xs => allDiscreteResolved Xs

/-- the guard implies full resolution -/
theorem resolveFull_of_guard : ∀ {tys : List Ty} (ds : CDen tys) {X : CEnc tys},
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
  | (.cplx :: _), .cons .cplx d ds, .cons .cplx _ Xs, h => by
    simp only [allDiscreteResolved] at h
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds h
    exact ⟨.cons .cplx d vs, by rw [resolveFull_cons_cplx, hvs]⟩
  | (.list _ :: _), .cons _ d ds, .cons _ _ Xs, h => by
    simp only [allDiscreteResolved] at h
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard ds h
    exact ⟨.cons _ d vs, by rw [resolveFull_cons_list, hvs]⟩

-- Interval evaluation (with argument-list evaluation).
mutual
def eval (c : Ctx) : {t : Ty} → Expr t → IEnv → t.Enc
  | _, .lit q, _ => Ival.ofRat c.prec q
  | _, .rlit q, _ => some q
  | _, .natLit n, _ => NIval.pt n
  | _, .intLit z, _ => ZIval.pt z
  | _, .clist xs, σ => some (evalList c σ xs)
  | _, .var t i, σ => σ.get t i
  | _, .c0 f, _ => f.ev c
  | _, .c1 f x, σ => f.ev c (x.eval c σ)
  | _, .c2 f x y, σ => f.ev c (x.eval c σ) (y.eval c σ)
  | _, @Expr.call tys r f xs, σ =>
    let X := evalCArgs c σ xs
    if allDiscreteResolved X then f.ev c X else r.top
  | _, .sum t n body, σ =>
    match NIval.isPoint (n.eval c σ) with
    | some N => sumLoop t c.prec (fun k => body.eval c (σ.push .nat (NIval.pt k))) N
    | none => t.top

/-- evaluate an argument list -/
def evalCArgs (c : Ctx) (σ : IEnv) : {tys : List Ty} → CArg tys → CEnc tys
  | _, .nil => .nil
  | (_ :: _), .cons t e es => .cons t (e.eval c σ) (evalCArgs c σ es)

/-- evaluate a list literal -/
def evalList (c : Ctx) (σ : IEnv) : {t : Ty} → ExprList t → List t.Enc
  | _, .nil => []
  | _, .cons x xs => x.eval c σ :: evalList c σ xs
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
  | _, .rlit q, _, _, _ => by
    simp only [eval, denote, Ty.Mem]
    exact fun _ h => Option.some_inj.mp h
  | _, .clist xs, _, _, h => by
    simp only [eval, denote, Ty.Mem]
    exact evalList_sound hc h xs
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
  | _, @Expr.call tys .nat f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .int f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .rat f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .real f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys .cplx f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
  | _, @Expr.call tys (.list _) f xs, ρ, σ, h =>
    eval_sound_call hc f xs (evalCArgs_sound hc h xs)
theorem evalCArgs_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    (hs : σ.Holds ρ) : ∀ {tys : List Ty} (xs : CArg tys),
    CEncHolds (evalCArgs c σ xs) (CArg.denoteArgs ρ xs)
  | _, .nil => by simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
  | _, .cons t e es => by
    simp only [evalCArgs, CArg.denoteArgs, CEncHolds]
    exact ⟨eval_sound hc e hs, evalCArgs_sound hc hs es⟩
theorem evalList_sound {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    (hs : σ.Holds ρ) : ∀ {t : Ty} (xs : ExprList t),
    List.Forall₂ (Ty.Mem t) (evalList c σ xs) (denoteList xs ρ)
  | _, .nil => by simp only [evalList, denoteList]; exact .nil
  | _, .cons x xs => by
    simp only [evalList, denoteList]
    exact .cons (eval_sound hc x hs) (evalList_sound hc hs xs)
theorem eval_sound_call {c : Ctx} (hc : c.Valid) {ρ : SEnv} {σ : IEnv}
    {tys : List Ty} {r : Ty}
    (f : CFn tys r) (xs : CArg tys)
    (hH : CEncHolds (evalCArgs c σ xs) (CArg.denoteArgs ρ xs)) :
    r.Mem ((Expr.call f xs).eval c σ) ((Expr.call f xs).denote ρ) := by
  simp only [eval, denote]
  split
  · rename_i hres
    obtain ⟨vs, hvs⟩ := resolveFull_of_guard (CArg.denoteArgs ρ xs) hres
    have hag := resolveFull_sound hH hvs
    have htv : toVal (CArg.denoteArgs ρ xs) = vs := toVal_agrees hag
    have hg : f.graph vs (f.fn' vs) := f.fn_spec vs
    rw [htv]
    exact f.sound c vs _ _ _ hc hg hH hag
  · exact r.mem_top _
end

theorem call_eq {tys : List Ty} {r : Ty}
    (f : CFn tys r) (xs : CArg tys) (ρ : SEnv)
    {vs : CVal tys} {ds : CDen tys} {y : r.Val}
    (hds : ds = CArg.denoteArgs ρ xs) (hag : Agree vs ds)
    (hg : f.graph vs y) :
    y = (Expr.call f xs).denote ρ := by
  simp only [denote]
  show y = f.fn' (toVal (CArg.denoteArgs ρ xs))
  rw [← hds, toVal_agrees hag]
  exact f.eq_fn hg

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

theorem rlit_eq (q : ℚ) (ρ : SEnv) {X : ℚ} (h : X = q) : X = (Expr.rlit q).denote ρ := h

theorem clist_nil_eq (t : Ty) (ρ : SEnv) :
    ([] : List t.Val) = (Expr.clist (ExprList.nil : ExprList t)).denote ρ := rfl

theorem clist_cons_eq {t : Ty} (x : Expr t) (xs : ExprList t) (ρ : SEnv)
    {v : t.Val} {vs : List t.Val}
    (hx : v = x.denote ρ) (hxs : vs = denoteList xs ρ) :
    v :: vs = (Expr.clist (ExprList.cons x xs)).denote ρ := by
  simp only [denote, denoteList]
  exact congrArg₂ _ hx hxs

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
