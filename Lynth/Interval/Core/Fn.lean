import Lynth.Interval.Core.Ctx

/-!
# Function records (the open registry's entries)

A function is described by a record holding its semantics **only in `Prop`
fields** (`graph`, `exu`, `sound`), so records mentioning noncomputable
functions such as `Real.exp` are still computable.  Always write records as
structure literals with the function inside `graph` (passing `Real.exp` to a
helper *function* would make the record noncomputable):

```lean
@[lynth_fn] def expFn : Fn1 .real .real where
  name := "exp"
  graph x y := y = Real.exp x
  exu := exu_eq _
  ev := expIval
  sound := fun c x y X hc hy hx => by cases hy; exact mem_expIval hc hx
```

See `docs/interval/03-expr-registry.md §3, §9`.
-/

namespace Lynth.Interval

/-- the graph of a function is functional -/
theorem exu_eq {α β : Type} (F : α → β) : ∀ x, ∃! y, y = F x :=
  fun x => ⟨F x, rfl, fun _ h => h⟩

theorem exu_eq₂ {α β γ : Type} (F : α → β → γ) : ∀ x y, ∃! z, z = F x y :=
  fun x y => ⟨F x y, rfl, fun _ h => h⟩

theorem exu_eq₀ {β : Type} (b : β) : ∃! y, y = b := ⟨b, rfl, fun _ h => h⟩

/-- nullary function (constant) -/
structure Fn0 (r : Ty) where
  name : String
  graph : r.Val → Prop
  exu : ∃! y, graph y
  ev : Ctx → r.Enc
  sound : ∀ (c : Ctx) (y : r.Val), c.Valid → graph y → r.Mem (ev c) y
  cost : Nat := 1

/-- unary function -/
structure Fn1 (a r : Ty) where
  name : String
  graph : a.Val → r.Val → Prop
  exu : ∀ x, ∃! y, graph x y
  ev : Ctx → a.Enc → r.Enc
  sound : ∀ (c : Ctx) (x : a.Val) (y : r.Val) (X : a.Enc),
    c.Valid → graph x y → a.Mem X x → r.Mem (ev c X) y
  cost : Nat := 1

/-- binary function -/
structure Fn2 (a b r : Ty) where
  name : String
  graph : a.Val → b.Val → r.Val → Prop
  exu : ∀ x y, ∃! z, graph x y z
  ev : Ctx → a.Enc → b.Enc → r.Enc
  sound : ∀ (c : Ctx) (x : a.Val) (y : b.Val) (z : r.Val) (X : a.Enc) (Y : b.Enc),
    c.Valid → graph x y z → a.Mem X x → b.Mem Y y → r.Mem (ev c X Y) z
  cost : Nat := 1

namespace Fn0
variable {r : Ty} (f : Fn0 r)
/-- the denoted value -/
noncomputable def val : r.Val := f.exu.exists.choose
theorem val_spec : f.graph f.val := f.exu.exists.choose_spec
theorem eq_val {y : r.Val} (h : f.graph y) : y = f.val := f.exu.unique h f.val_spec
end Fn0

namespace Fn1
variable {a r : Ty} (f : Fn1 a r)
/-- the denoted function -/
noncomputable def fn (x : a.Val) : r.Val := (f.exu x).exists.choose
theorem fn_spec (x : a.Val) : f.graph x (f.fn x) := (f.exu x).exists.choose_spec
theorem eq_fn {x : a.Val} {y : r.Val} (h : f.graph x y) : y = f.fn x :=
  (f.exu x).unique h (f.fn_spec x)
end Fn1

namespace Fn2
variable {a b r : Ty} (f : Fn2 a b r)
/-- the denoted function -/
noncomputable def fn (x : a.Val) (y : b.Val) : r.Val := (f.exu x y).exists.choose
theorem fn_spec (x : a.Val) (y : b.Val) : f.graph x y (f.fn x y) := (f.exu x y).exists.choose_spec
theorem eq_fn {x : a.Val} {y : b.Val} {z : r.Val} (h : f.graph x y z) : z = f.fn x y :=
  (f.exu x y).unique h (f.fn_spec x y)
end Fn2

end Lynth.Interval
