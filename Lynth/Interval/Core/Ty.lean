import Lynth.Interval.Num.CBox
import Lynth.Interval.Num.NIval
import Lynth.Interval.Num.ZIval

/-!
# Value types of the interval AST

`Ty` indexes the typed expression language: natural numbers, integers, reals,
complex numbers, exact rationals and homogeneous lists, with their semantic
carriers (`Ty.Val`) and enclosures (`Ty.Enc`).  It is the single type index:
custom-function positions are typed by `Ty` directly (there is no separate
`CTy`); `.rat` positions carry exact values (`Option ℚ`, unresolved is `none`)
and `.list t` positions carry pointwise enclosures.
See `docs/interval/03-expr-registry.md §1`.
-/

namespace Lynth.Interval

inductive Ty | nat | int | real | cplx | rat | list (t : Ty)
deriving Repr, DecidableEq, Inhabited

namespace Ty

/-- semantic carrier -/
@[reducible] def Val : Ty → Type
  | .nat => ℕ
  | .int => ℤ
  | .real => ℝ
  | .cplx => ℂ
  | .rat => ℚ
  | .list t => List t.Val

/-- computational enclosure (`rat` is exact-or-unknown; lists are
pointwise-or-unknown: `none` is the trivial enclosure) -/
@[reducible] def Enc : Ty → Type
  | .nat => NIval
  | .int => ZIval
  | .real => Ival
  | .cplx => CBox
  | .rat => Option ℚ
  | .list t => Option (List t.Enc)

/-- membership of a value in an enclosure -/
def Mem : (t : Ty) → t.Enc → t.Val → Prop
  | .nat, I, n => n ∈ I
  | .int, I, z => z ∈ I
  | .real, I, x => x ∈ I
  | .cplx, B, z => z ∈ B
  | .rat, o, v => ∀ q, o = some q → v = q
  | .list _, none, _ => True
  | .list t, some X, v => List.Forall₂ (Mem t) X v

/-- the trivial enclosure -/
def top : (t : Ty) → t.Enc
  | .nat => NIval.top
  | .int => ZIval.top
  | .real => Ival.top
  | .cplx => CBox.top
  | .rat => none
  | .list _ => none

theorem mem_top : (t : Ty) → (v : t.Val) → t.Mem (t.top) v
  | .nat, n => NIval.mem_top n
  | .int, z => ZIval.mem_top z
  | .real, x => Ival.mem_top x
  | .cplx, z => CBox.mem_top z
  | .rat, v => fun _ h => nomatch h
  | .list _, _ => trivial

/-- pointwise addition on value lists (missing tails treated as zero).
The element operation is explicit: nothing here relies on typeclass
resolution, so all uses stay syntactic. -/
def listAdd (t : Ty) (add : t.Val → t.Val → t.Val) :
    List t.Val → List t.Val → List t.Val
  | [], ys => ys
  | x :: xs, ys =>
    match ys with
    | [] => x :: xs
    | y :: ys => add x y :: listAdd t add xs ys

/-- scalar multiplication on value lists -/
def listNsmul (t : Ty) (add : t.Val → t.Val → t.Val) :
    ℕ → List t.Val → List t.Val
  | 0, _ => []
  | n + 1, xs => listAdd t add (listNsmul t add n xs) xs

def listAddCommMonoid (t : Ty) (F : t.Val → t.Val → t.Val)
    (comm : ∀ x y, F x y = F y x)
    (assoc : ∀ x y z, F (F x y) z = F x (F y z)) :
    AddCommMonoid (List t.Val) where
  zero := []
  add := listAdd t F
  nsmul := listNsmul t F
  zero_add ys := by induction ys with
    | nil => rfl
    | cons _ _ _ => rfl
  add_zero xs := by induction xs with
    | nil => rfl
    | cons _ _ _ => rfl
  add_comm xs ys := by
    change t.listAdd F xs ys = t.listAdd F ys xs
    induction xs generalizing ys with
    | nil => cases ys with | nil => rfl | cons _ _ => rfl
    | cons x xs ih => cases ys with
      | nil => rfl
      | cons y ys =>
        change F x y :: t.listAdd F xs ys = F y x :: t.listAdd F ys xs
        rw [comm x y, ih ys]
  add_assoc xs ys zs := by
    change t.listAdd F (t.listAdd F xs ys) zs
      = t.listAdd F xs (t.listAdd F ys zs)
    induction xs generalizing ys zs with
    | nil => cases ys with | nil => rfl | cons _ _ => rfl
    | cons x xs ih => cases ys with
      | nil => rfl
      | cons y ys => cases zs with
        | nil => rfl
        | cons z zs =>
          change F (F x y) z :: t.listAdd F (t.listAdd F xs ys) zs
            = F x (F y z) :: t.listAdd F xs (t.listAdd F ys zs)
          rw [assoc x y z, ih ys zs]
  nsmul_zero xs := by
    change t.listNsmul F 0 xs = []
    rfl
  nsmul_succ n xs := by
    change t.listNsmul F (n + 1) xs
      = t.listAdd F (t.listNsmul F n xs) xs
    rfl

/-- dummy value (for `CFn.fn` placeholders, which are never applied:
denotation uses `fn'`, evaluation uses `ev`) -/
def defaultVal : (t : Ty) → t.Val
  | .nat => 0
  | .int => 0
  | .real => 0
  | .cplx => 0
  | .rat => 0
  | .list _ => []

instance instAddCommMonoid : (t : Ty) → AddCommMonoid t.Val
  | .nat => inferInstanceAs (AddCommMonoid ℕ)
  | .int => inferInstanceAs (AddCommMonoid ℤ)
  | .real => inferInstanceAs (AddCommMonoid ℝ)
  | .cplx => inferInstanceAs (AddCommMonoid ℂ)
  | .rat => inferInstanceAs (AddCommMonoid ℚ)
  | .list t => by
    haveI hinst : AddCommMonoid t.Val := instAddCommMonoid t
    exact listAddCommMonoid t (· + ·) (fun x y => add_comm x y)
      (fun x y z => add_assoc x y z)

/-- exact zero enclosure -/
def zeroE : (t : Ty) → t.Enc
  | .nat => NIval.pt 0
  | .int => ZIval.pt 0
  | .real => Ival.zero
  | .cplx => ⟨Ival.zero, Ival.zero⟩
  | .rat => some 0
  | .list _ => some []

/-- pointwise enclosure addition with an explicit element operation -/
def zipAddE (t : Ty) (f : t.Enc → t.Enc → t.Enc) :
    List t.Enc → List t.Enc → List t.Enc
  | [], Ys => Ys
  | Xs, [] => Xs
  | x :: xs, y :: ys => f x y :: zipAddE t f xs ys

/-- sum of enclosures at precision `p` (lists: pointwise when both known) -/
def addE : (t : Ty) → Nat → t.Enc → t.Enc → t.Enc
  | .nat, _, I, J => NIval.add I J
  | .int, _, I, J => ZIval.add I J
  | .real, p, I, J => Ival.add p I J
  | .cplx, p, A, B => CBox.add p A B
  | .rat, _, o₁, o₂ => o₁.bind fun a => o₂.bind fun b => some (a + b)
  | .list _, _, none, _ => none
  | .list _, _, some _, none => none
  | .list t, p, some A, some B => some (zipAddE t (t.addE p) A B)

theorem zipAddE_mem (t : Ty) (p : Nat) (F : t.Val → t.Val → t.Val)
    (hadd : ∀ {A B : t.Enc} {a b : t.Val},
      t.Mem A a → t.Mem B b → t.Mem (t.addE p A B) (F a b)) :
    ∀ (A : List t.Enc) (a : List t.Val),
    List.Forall₂ (Ty.Mem t) A a →
    ∀ (B : List t.Enc) (b : List t.Val),
    List.Forall₂ (Ty.Mem t) B b →
    List.Forall₂ (Ty.Mem t) (zipAddE t (t.addE p) A B) (t.listAdd F a b) := by
  intro A a ha
  induction ha with
  | nil =>
    intro B b hb
    cases hb with
    | nil => exact List.Forall₂.nil
    | cons h1 ht => exact List.Forall₂.cons h1 ht
  | cons h1 htA ih =>
    intro B b hb
    cases hb with
    | nil => exact List.Forall₂.cons h1 htA
    | cons h2 hb2 =>
      exact List.Forall₂.cons (hadd h1 h2) (ih _ _ hb2)

theorem mem_zeroE : (t : Ty) → t.Mem t.zeroE 0
  | .nat => NIval.mem_pt 0
  | .int => ZIval.mem_pt 0
  | .real => Ival.mem_zero
  | .cplx => ⟨by rw [Complex.zero_re]; exact Ival.mem_zero, by rw [Complex.zero_im]; exact Ival.mem_zero⟩
  | .rat => fun _ h => Option.some_inj.mp h
  | .list t => by
    simp only [Mem, zeroE]
    exact List.Forall₂.nil

theorem mem_addE : (t : Ty) → {p : Nat} → {A B : t.Enc} → {a b : t.Val} →
    t.Mem A a → t.Mem B b → t.Mem (t.addE p A B) (a + b)
  | .nat, _, _, _, _, _, ha, hb => NIval.mem_add ha hb
  | .int, _, _, _, _, _, ha, hb => ZIval.mem_add ha hb
  | .real, _, _, _, _, _, ha, hb => Ival.mem_add ha hb
  | .cplx, _, _, _, _, _, ha, hb => CBox.mem_add ha hb
  | .rat, _, o₁, o₂, _, _, ha, hb =>
    fun q hq => by
      cases o₁ with
      | none => exact absurd hq (by simp [addE])
      | some a' =>
        cases o₂ with
        | none => exact absurd hq (by simp [addE])
        | some b' =>
          have e := Option.some_inj.mp (by simpa [addE] using hq)
          rw [ha _ rfl, hb _ rfl]
          exact e
  | .list _, _, none, _, _, _, _, _ => by simp only [addE, Mem]
  | .list _, _, some _, none, _, _, _, _ => by simp only [addE, Mem]
  | .list t, _, some A, some B, a, b, ha, hb =>
    have ha' : List.Forall₂ (Ty.Mem t) A a := ha
    have hb' : List.Forall₂ (Ty.Mem t) B b := hb
    zipAddE_mem t _ (· + ·) (t.mem_addE) _ _ ha' _ _ hb'

/-- is the enclosure bounded -/
def isFinite : (t : Ty) → t.Enc → Bool
  | .nat, I => I.hi.isSome
  | .int, I => I.hi.isSome
  | .real, I => I.isFinite
  | .cplx, B => B.isFinite
  | .rat, o => o.isSome
  | .list t, none => false
  | .list t, some X => X.all (isFinite t)

end Ty

end Lynth.Interval
