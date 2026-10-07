import Mathlib
import Lynth

open Lynth.Interval

/-! # User-defined n-ary custom functions (N1–N10).

End-to-end coverage for `CFn` over `Nat`/`Int`/`Rat`/`Real`: registry
(`@[lynth_cfn]`), reification (`Expr.call` nodes, rat lit-or-chain rule),
evaluation (discrete top-guard), and discrete/closed witnesses.
Ground truth checked against kernel computation.
-/

/-- N1–N3 setup: 2-ary Nat addition, 2-ary Int multiply, 3-ary Nat combo. -/
def myadd (a b : ℕ) : ℕ := a + b
def mymul (a b : ℤ) : ℤ := a * b
def myf3 (a b c : ℕ) : ℕ := a + 2 * b + 3 * c

@[lynth_cfn] def myaddR : CFn [.nat, .nat] .nat :=
  CFn.ofFn [.nat, .nat] .nat myadd "myadd" 1
@[lynth_cfn] def mymulR : CFn [.int, .int] .int :=
  CFn.ofFn [.int, .int] .int mymul "mymul" 1
@[lynth_cfn] def myf3R : CFn [.nat, .nat, .nat] .nat :=
  CFn.ofFn [.nat, .nat, .nat] .nat myf3 "myf3" 1

set_option maxHeartbeats 20000 in
-- N1: 2-ary Nat, bare discrete witness. 7
def nary_nat_add : { n : Nat // n = myadd 3 4 } := by
  lynth
#print axioms nary_nat_add
#eval nary_nat_add.1

set_option maxHeartbeats 20000 in
-- N2: 2-ary Int with negatives, bare discrete witness. -12
def nary_int_mul : { s : Int // s = mymul (-3) 4 } := by
  lynth
#print axioms nary_int_mul
#eval nary_int_mul.1

set_option maxHeartbeats 20000 in
-- N3: 3-ary Nat, bare discrete witness. 14
def nary_nat_3ary : { n : Nat // n = myf3 1 2 3 } := by
  lynth
#print axioms nary_nat_3ary
#eval nary_nat_3ary.1

/-- N4 setup: manual 2-ary Real entry (`x² + y²`, composed interval ops). -/
def mysqadd (x y : ℝ) : ℝ := x * x + y * y

def mysqadd_ev (c : Ctx) : CEnc [.real, .real] → Ival
  | .cons .real X (.cons .real Y .nil) =>
    Ival.add c.prec (Ival.mul c.prec X X) (Ival.mul c.prec Y Y)

theorem mysqadd_sound (c : Ctx) :
    ∀ (vs : CVal [.real, .real]) (ds : CDen [.real, .real]) (y' : ℝ) (y : ℝ)
      (X : CEnc [.real, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.real, .real] .real mysqadd vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (mysqadd_ev c X) y
  | .cons .real x (.cons .real y .nil),
    .cons .real dx (.cons .real dy .nil), _, _,
    .cons .real IX (.cons .real IY .nil), _, hg, hout, hh, hag => by
    simp only [castOut] at hout
    subst hout
    have hxM := hh.1; have hyM := hh.2.1
    have hxE := hag.1; have hyE := hag.2.1
    simp only [mysqadd_ev]
    subst hxE; subst hyE
    simp only [applyCurried] at hg
    subst hg
    unfold mysqadd
    exact Ival.mem_add (Ival.mem_mul hxM hxM) (Ival.mem_mul hyM hyM)

@[lynth_cfn] def mysqaddR : CFn [.real, .real] .real :=
  CFn.manual [.real, .real] .real mysqadd mysqadd_ev mysqadd_sound "mysqadd" 10

set_option maxHeartbeats 60000 in
-- N4: manual 2-ary Real via the closed procedure. 13
def nary_real_manual : { x : Rat //
    abs (mysqadd 2 3 - x) < 1 / 1000 } := by
  lynth
#print axioms nary_real_manual
#eval nary_real_manual.1

/-- N5/N7 setup: rational parameter and rational result. -/
def myratmul (q : ℚ) (x : ℝ) : ℝ := q * x

def myratmul_ev (c : Ctx) : CEnc [.rat, .real] → Ival
  | .cons .rat o (.cons .real Y .nil) =>
    match o with
    | some q => Ival.mul c.prec (Ival.ofRat c.prec q) Y
    | none => Ival.top

theorem myratmul_sound (c : Ctx) :
    ∀ (vs : CVal [.rat, .real]) (ds : CDen [.rat, .real]) (y' y : ℝ)
      (X : CEnc [.rat, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.rat, .real] .real myratmul vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (myratmul_ev c X) y
  | .cons .rat v (.cons .real x .nil),
    .cons .rat d (.cons .real dx .nil), _, _,
    .cons .rat o (.cons .real Y .nil), _, hg, hout, hh, hag => by
    simp only [castOut] at hout
    subst hout
    have hm := hh.1; have hrest := hh.2
    have hag1 := hag.1; have hag2 := hag.2
    have hyM := hrest.1; have hxE := hag2.1
    match hq : o with
    | some q =>
      simp only [myratmul_ev]
      have hd : d = (q : ℝ) := hm _ rfl
      simp only [ratOut] at hag1
      have hqv : q = v := Rat.cast_injective (hd.symm.trans hag1)
      subst hqv; subst hxE
      simp only [applyCurried] at hg
      subst hg
      unfold myratmul
      exact Ival.mem_mul (Ival.mem_ofRat _ _) hyM
    | none =>
      simp only [myratmul_ev]
      exact Ival.mem_top _

@[lynth_cfn] def myratmulR : CFn [.rat, .real] .real :=
  CFn.manual [.rat, .real] .real myratmul myratmul_ev myratmul_sound "myratmul" 5

def myhalf (n : ℕ) : ℚ := n / 2

@[lynth_cfn] def myhalfR : CFn [.nat] .rat :=
  CFn.ofFn [.nat] .rat myhalf "myhalf" 1

def myqmul (q : ℚ) (x : ℝ) : ℝ := q * x + 1

def myqmul_ev (c : Ctx) : CEnc [.rat, .real] → Ival
  | .cons .rat o (.cons .real Y .nil) =>
    match o with
    | some q => Ival.add c.prec (Ival.mul c.prec (Ival.ofRat c.prec q) Y) (Ival.ofRat c.prec 1)
    | none => Ival.top

theorem myqmul_sound (c : Ctx) :
    ∀ (vs : CVal [.rat, .real]) (ds : CDen [.rat, .real]) (y' y : ℝ)
      (X : CEnc [.rat, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.rat, .real] .real myqmul vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (myqmul_ev c X) y
  | .cons .rat v (.cons .real x .nil),
    .cons .rat d (.cons .real dx .nil), _, _,
    .cons .rat o (.cons .real Y .nil), _, hg, hout, hh, hag => by
    simp only [castOut] at hout
    subst hout
    have hm := hh.1; have hrest := hh.2
    have hag1 := hag.1; have hag2 := hag.2
    have hyM := hrest.1; have hxE := hag2.1
    match hq : o with
    | some q =>
      simp only [myqmul_ev]
      have hd : d = (q : ℝ) := hm _ rfl
      simp only [ratOut] at hag1
      have hqv : q = v := Rat.cast_injective (hd.symm.trans hag1)
      subst hqv; subst hxE
      simp only [applyCurried] at hg
      subst hg
      unfold myqmul
      exact Ival.mem_add (Ival.mem_mul (Ival.mem_ofRat _ _) hyM)
        (by simpa using Ival.mem_ofRat c.prec (1 : ℚ))
    | none =>
      simp only [myqmul_ev]
      exact Ival.mem_top _

@[lynth_cfn] def myqmulR : CFn [.rat, .real] .real :=
  CFn.manual [.rat, .real] .real myqmul myqmul_ev myqmul_sound "myqmul" 5

set_option maxHeartbeats 60000 in
-- N5: rational parameter (closed literal). 3
def nary_rat_param : { x : Rat //
    abs (myratmul (3 / 2) 2 - x) < 1 / 1000 } := by
  lynth
#print axioms nary_rat_param
#eval nary_rat_param.1

set_option maxHeartbeats 60000 in
-- N6: rational result under a cast. 1/2
def nary_rat_result : { x : Rat //
    abs (((myhalf 3 : ℚ) : ℝ) - x) < 1 / 1000 } := by
  lynth
#print axioms nary_rat_result
#eval nary_rat_result.1

set_option maxHeartbeats 60000 in
-- N7: nested rat result inside a rat parameter. 4
def nary_rat_nest : { x : Rat //
    abs (myqmul (myhalf 3) 2 - x) < 1 / 1000 } := by
  lynth
#print axioms nary_rat_nest
#eval nary_rat_nest.1

set_option maxHeartbeats 60000 in
-- N8: manual nested in manual with a rational parameter. 5
def nary_nest_manual : { x : Rat //
    abs (mysqadd (myratmul (1 / 2) 4) 1 - x) < 1 / 1000 } := by
  lynth
#print axioms nary_nest_manual
#eval nary_nest_manual.1

/-- N9 setup: noncomputable marker with an arbitrary internal type. -/
inductive MyTag where
  | A : MyTag
  | B : MyTag
  deriving DecidableEq, Repr

noncomputable def mywsum (a b : ℕ) : ℕ :=
  let tags : List MyTag := [MyTag.A, MyTag.B]
  a + b + tags.length

@[lynth_cfn] noncomputable def mywsumR : CFn [.nat, .nat] .nat :=
  CFn.ofFn [.nat, .nat] .nat mywsum "mywsum" 1

set_option maxHeartbeats 20000 in
-- N9: noncomputable with internal custom type, bare witness. 9
noncomputable def nary_noncomputable : { n : Nat // n = mywsum 3 4 } := by
  lynth
#print axioms nary_noncomputable
-- `#eval[!]` cannot compile the noncomputable marker; the witness value is
-- checked definitionally instead (bare candidate is the literal `9`).
example : nary_noncomputable.1 = 9 := rfl

/-- N10 setup: 4-ary over all four `CTy`s. -/
def myall (a : ℕ) (z : ℤ) (q : ℚ) (x : ℝ) : ℝ := (a : ℝ) + (z : ℝ) + (q : ℝ) + x

def myall_ev (c : Ctx) : CEnc [.nat, .int, .rat, .real] → Ival
  | .cons .nat A (.cons .int Z (.cons .rat o (.cons .real Y .nil))) =>
    match o with
    | some q =>
      Ival.add c.prec
        (Ival.add c.prec (Ival.add c.prec (NIval.toIval A) (ZIval.toIval Z))
          (Ival.ofRat c.prec q)) Y
    | none => Ival.top

theorem myall_sound (c : Ctx) :
    ∀ (vs : CVal [.nat, .int, .rat, .real]) (ds : CDen [.nat, .int, .rat, .real])
      (y' y : ℝ) (X : CEnc [.nat, .int, .rat, .real]) (hc : c.Valid)
      (hg : y' = applyCurried [.nat, .int, .rat, .real] .real myall vs)
      (hout : castOut .real y' = y)
      (hh : CEncHolds X ds) (hag : Agree vs ds),
    Ival.Mem (myall_ev c X) y
  | .cons .nat a (.cons .int z (.cons .rat v (.cons .real x .nil))),
    .cons .nat da (.cons .int dz (.cons .rat d (.cons .real dx .nil))), _, _,
    .cons .nat A (.cons .int Z (.cons .rat o (.cons .real Y .nil))),
    _, hg, hout, hh, hag => by
    simp only [castOut] at hout
    subst hout
    have hAM := hh.1; have hrest1 := hh.2
    have hZM := hrest1.1; have hrest2 := hrest1.2
    have hm := hrest2.1; have hyM := hrest2.2.1
    have haE := hag.1; have hagR1 := hag.2
    have hzE := hagR1.1; have hagR2 := hagR1.2
    have hag1 := hagR2.1; have hxE := hagR2.2.1
    match hq : o with
    | some q =>
      simp only [myall_ev]
      have hd : d = (q : ℝ) := hm _ rfl
      simp only [ratOut] at hag1
      have hqv : q = v := Rat.cast_injective (hd.symm.trans hag1)
      subst hqv; subst haE; subst hzE; subst hxE
      simp only [applyCurried] at hg
      subst hg
      unfold myall
      exact Ival.mem_add
        (Ival.mem_add (Ival.mem_add (NIval.mem_toIval hAM) (ZIval.mem_toIval hZM))
          (Ival.mem_ofRat _ _)) hyM
    | none =>
      simp only [myall_ev]
      exact Ival.mem_top _

@[lynth_cfn] def myallR : CFn [.nat, .int, .rat, .real] .real :=
  CFn.manual [.nat, .int, .rat, .real] .real myall myall_ev myall_sound "myall" 10

set_option maxHeartbeats 60000 in
-- N10: 4-ary mixed, all `CTy`s. 2.5
def nary_mixed_4ary : { x : Rat //
    abs (myall 1 (-2) (1 / 2) 3 - x) < 1 / 1000 } := by
  lynth
#print axioms nary_mixed_4ary
#eval nary_mixed_4ary.1
