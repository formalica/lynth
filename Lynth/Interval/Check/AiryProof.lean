module

import all Lynth.Interval.Core.Const
import all Lynth.Interval.Fns.Gamma
public import Lean.Elab.Tactic.Cbv
public meta import Lean
public meta import Mathlib.Algebra.Group.Nat.Defs
public meta import Mathlib.Algebra.Group.Int.Defs
public meta import Mathlib.Algebra.Group.Monoid

public section
/-!
Proof-producing arithmetic for the Airy normalization certificate.

Closed integer calculations use reflexivity or small certificates. Long series,
Bernoulli tables, and rising products are checked a few steps at a time to keep
proof evaluation within the stack limit. The procedures are enabled by opening
`Lynth.Interval.AiryProof.Kernel` as a scope.
-/

open Lean Meta Sym Sym.Simp

private meta def memoProof (h : Lean.Expr) : MetaM Lean.Expr := do
  let t ← Meta.inferType h
  if t.hasFVar || t.hasMVar then return h
  let name ← Meta.mkAuxLemma [] t h (kind? := `lynth_airy_step)
  return mkConst name

namespace Lynth.Interval.AiryProof.Kernel
private meta def natVal? (e : Lean.Expr) : Option Nat :=
  match (Sym.getNatValue? e).run with
  | some n => some n
  | none => match e with | .lit (.natVal n) => some n | _ => none
private meta def intVal? (e : Lean.Expr) : Option Int :=
  match (Sym.getIntValue? e).run with
  | some n => some n
  | none => match_expr e with
    | Int.ofNat n => Int.ofNat <$> natVal? n
    | Int.negSucc n => Int.negSucc <$> natVal? n
    | _ => none

scoped cbv_simproc ↓ rationalLiteral ((_ : Rat) / (_ : Rat)) := fun e => do
  if (Sym.getRatValue? e).isSome then return .rfl (done := true)
  return .rfl
scoped cbv_simproc ↓ rationalNum ((_: Rat).num) := fun e => do
  let a := match e with | .proj _ _ a => a | _ => e.appArg!
  let some q := Sym.getRatValue? a | return .rfl
  let v ← share (toExpr q.num)
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc ↓ rationalDen ((_: Rat).den) := fun e => do
  let a := match e with | .proj _ _ a => a | _ => e.appArg!
  let some q := Sym.getRatValue? a | return .rfl
  let v ← share (toExpr q.den)
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc ↓ rationalProjections ((_ : Nat)) := fun e => do
  let .proj ``Rat idx a := e | return .rfl
  let some q := Sym.getRatValue? a | return .rfl
  let v ← share (if idx == 0 then toExpr q.num else toExpr q.den)
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval ratRecord (Rat.mk' _ _ _ _) := fun e => do
  let_expr Rat.mk' n d _ _ := e | return .rfl
  let some nv := intVal? n | return .rfl
  let some dv := natVal? d | return .rfl
  let v ← share (toExpr ((nv : Rat) / dv))
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval ratOfInt (Rat.ofInt _) := fun e => do
  let_expr Rat.ofInt n := e | return .rfl
  let some nv := intVal? n | return .rfl
  let v ← share (toExpr (nv : Rat))
  return .step v (← Meta.mkEqRefl v) (done := true)
private theorem bitLength_from_bounds (n k : Nat) (hn : n ≠ 0) (hk : k ≤ 65536)
    (hlo : 2 ^ (k - 1) ≤ n) (hhi : n < 2 ^ k) :
    Lynth.Interval.Vendor.Dyadic.natBitLength n = k := by
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k = 0 := by omega
    subst k
    norm_num at hhi
    omega
  have hl := (Nat.le_log2 hn).mpr hlo
  have hh := (Nat.log2_lt hn).mpr hhi
  have he : n.log2 + 1 = k := by omega
  rw [Lynth.Interval.Vendor.Dyadic.natBitLength_eq_native]
  simpa [Lynth.Interval.Vendor.Dyadic.natBitLengthNative, hn, he] using hk
private theorem bitLength_bool (n k : Nat)
    (hn : decide (n ≠ 0) = true) (hk : decide (k ≤ 65536) = true)
    (hlo : decide (2 ^ (k - 1) ≤ n) = true) (hhi : decide (n < 2 ^ k) = true) :
    Lynth.Interval.Vendor.Dyadic.natBitLength n = k :=
  bitLength_from_bounds n k (of_decide_eq_true hn) (of_decide_eq_true hk)
    (of_decide_eq_true hlo) (of_decide_eq_true hhi)
scoped cbv_simproc cbv_eval fastBitLength (Lynth.Interval.Vendor.Dyadic.natBitLength _) := fun e => do
  let_expr Lynth.Interval.Vendor.Dyadic.natBitLength a := e | return .rfl
  let some av := Sym.getNatValue? a | return .rfl
  if av == 0 then
    let v ← share (toExpr (0 : Nat))
    return .step v (← Meta.mkEqRefl v) (done := true)
  let kv := av.log2 + 1
  if kv > 65536 then return .rfl
  let k ← share (toExpr kv)
  let tr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let h := mkAppN (mkConst ``bitLength_bool) #[a,k,tr,tr,tr,tr]
  return .step k h (done := true)
private theorem pow2Nat_eq (k : Nat) : Lynth.Interval.Vendor.Dyadic.pow2Nat k = 2 ^ k := by
  simp [Lynth.Interval.Vendor.Dyadic.pow2Nat, Nat.shiftLeft_eq]
scoped cbv_simproc cbv_eval fastPow2 (Lynth.Interval.Vendor.Dyadic.pow2Nat _) := fun e => do
  let_expr Lynth.Interval.Vendor.Dyadic.pow2Nat a := e | return .rfl
  let some av := natVal? a | return .rfl
  let v ← share (toExpr (2 ^ av : Nat))
  let h ← mkAppM ``pow2Nat_eq #[a]
  let h ← Meta.mkEqTrans h (← Meta.mkEqRefl v)
  return .step v h (done := true)
scoped cbv_simproc cbv_eval bigNatPow ((_ : Nat) ^ (_ : Nat)) := evalGround { maxExponent := 65536 }



scoped cbv_simproc cbv_eval directNatadd (Nat.add _ _) := fun e => do
  let_expr Nat.add a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av + bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatsub (Nat.sub _ _) := fun e => do
  let_expr Nat.sub a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av - bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatmul (Nat.mul _ _) := fun e => do
  let_expr Nat.mul a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av * bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatdiv (Nat.div _ _) := fun e => do
  let_expr Nat.div a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av / bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatmod (Nat.mod _ _) := fun e => do
  let_expr Nat.mod a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av % bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatpow (Nat.pow _ _) := fun e => do
  let_expr Nat.pow a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av ^ bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directNatgcd (Nat.gcd _ _) := fun e => do
  let_expr Nat.gcd a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (Nat.gcd av bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directIntadd (Int.add _ _) := fun e => do
  let_expr Int.add a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := intVal? b | return .rfl
  let v ← share (toExpr (av + bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directIntsub (Int.sub _ _) := fun e => do
  let_expr Int.sub a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := intVal? b | return .rfl
  let v ← share (toExpr (av - bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directIntmul (Int.mul _ _) := fun e => do
  let_expr Int.mul a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := intVal? b | return .rfl
  let v ← share (toExpr (av * bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directIntediv (Int.ediv _ _) := fun e => do
  let_expr Int.ediv a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := intVal? b | return .rfl
  let v ← share (toExpr (av / bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directIntemod (Int.emod _ _) := fun e => do
  let_expr Int.emod a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := intVal? b | return .rfl
  let v ← share (toExpr (av % bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directRatadd (Rat.add _ _) := fun e => do
  let_expr Rat.add a b := e | return .rfl
  let some av := Sym.getRatValue? a | return .rfl
  let some bv := Sym.getRatValue? b | return .rfl
  let v ← share (toExpr (av + bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directRatsub (Rat.sub _ _) := fun e => do
  let_expr Rat.sub a b := e | return .rfl
  let some av := Sym.getRatValue? a | return .rfl
  let some bv := Sym.getRatValue? b | return .rfl
  let v ← share (toExpr (av - bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directRatmul (Rat.mul _ _) := fun e => do
  let_expr Rat.mul a b := e | return .rfl
  let some av := Sym.getRatValue? a | return .rfl
  let some bv := Sym.getRatValue? b | return .rfl
  let v ← share (toExpr (av * bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval directRatdiv (Rat.div _ _) := fun e => do
  let_expr Rat.div a b := e | return .rfl
  let some av := Sym.getRatValue? a | return .rfl
  let some bv := Sym.getRatValue? b | return .rfl
  let v ← share (toExpr (av / bv))
  return .step v (← Meta.mkEqRefl v) (done := true)

scoped cbv_simproc cbv_eval bigIntPow ((_ : Int) ^ (_ : Nat)) := evalGround { maxExponent := 65536 }
scoped cbv_simproc cbv_eval directIntPow (Int.pow _ _) := fun e => do
  let_expr Int.pow a b := e | return .rfl
  let some av := intVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av ^ bv))
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval directNatble (Nat.ble _ _) := fun e => do
  let_expr Nat.ble a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (decide (av ≤ bv)))
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval directNatbeq (Nat.beq _ _) := fun e => do
  let_expr Nat.beq a b := e | return .rfl
  let some av := natVal? a | return .rfl
  let some bv := natVal? b | return .rfl
  let v ← share (toExpr (av == bv))
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval directIntnatAbs (Int.natAbs _) := fun e => do
  let_expr Int.natAbs a := e | return .rfl
  let some av := intVal? a | return .rfl
  let v ← share (toExpr (Int.natAbs av))
  return .step v (← Meta.mkEqRefl v) (done := true)
scoped cbv_simproc cbv_eval directInttoNat (Int.toNat _) := fun e => do
  let_expr Int.toNat a := e | return .rfl
  let some av := intVal? a | return .rfl
  let v ← share (toExpr (Int.toNat av))
  return .step v (← Meta.mkEqRefl v) (done := true)
end Lynth.Interval.AiryProof.Kernel
open Lynth.Interval
namespace Lynth.Interval.AiryProof.Kernel

private theorem serLoop_stopped (p : Nat) (step : Nat → Ival → Ival)
    (small : Ival → Bool) (n : Nat) (st : SerState) (h : small st.T = true) :
    serLoop p step small n st = st := by
  cases n <;> simp [serLoop, h]
private theorem serLoop_add (p : Nat) (step : Nat → Ival → Ival)
    (small : Ival → Bool) (m n : Nat) (st : SerState) :
    serLoop p step small (m + n) st = serLoop p step small n (serLoop p step small m st) := by
  induction m generalizing st with
  | zero => simp [serLoop]
  | succ m ih =>
    rw [Nat.succ_add, serLoop, serLoop]
    split
    · rename_i h
      exact (serLoop_stopped p step small n st h).symm
    · exact ih _
scoped cbv_simproc cbv_eval seriesChunks (serLoop _ _ _ _ _) := fun e => do
  let_expr serLoop p step small fuel st := e | return .rfl
  let some fv := Sym.getNatValue? fuel | return .rfl
  if fv ≤ 8 then return .rfl
  let mut fuelV := fv
  let mut state := st
  let mut proof ← Meta.mkEqRefl e
  let base := mkApp3 (mkConst ``serLoop) p step small
  while fuelV > 0 do
    let m := min 8 fuelV
    let rem := fuelV - m
    let chunk := mkApp2 base (toExpr m) state
    let r ← Lean.Meta.Tactic.Cbv.cbvEntry chunk
    let next := r.getResultExpr chunk
    if next == state then
      let sm := mkApp small (mkProj ``SerState 1 state)
      let sr ← Lean.Meta.Tactic.Cbv.cbvEntry sm
      if let some true := (Sym.getBoolValue? (sr.getResultExpr sm)).run then
        let hp ← match sr with
          | .step _ h .. => pure h
          | _ => Meta.mkEqRefl sm
        let stop ← mkAppM ``serLoop_stopped #[p,step,small,toExpr fuelV,state,hp]
        let finalProof ← memoProof (← Meta.mkEqTrans proof stop)
        return .step state finalProof (done := true)
    let ch ← match r with
      | .step _ h .. => pure h
      | _ => Meta.mkEqRefl chunk
    let split ← mkAppM ``serLoop_add #[p,step,small,toExpr m,toExpr rem,state]
    let congr ← Meta.mkCongrArg (mkApp base (toExpr rem)) ch
    let h ← Meta.mkEqTrans split congr
    proof ← memoProof (← Meta.mkEqTrans proof h)
    state := next
    fuelV := rem
  let finalProof ← Meta.mkEqTrans proof (← Meta.mkEqRefl state)
  return .step state finalProof (done := true)
end Lynth.Interval.AiryProof.Kernel

open Lynth.Interval.Fns
namespace Lynth.Interval.AiryProof.Kernel
private def dot : List Nat → List ℚ → ℚ
  | List.cons rowHead rowTail, List.cons valHead valTail =>
    (rowHead : ℚ) * valHead + dot rowTail valTail
  | _, _ => 0
private theorem dot_eq (row : List Nat) (vals : List ℚ) :
    dot row vals = ∑ k ∈ Finset.range vals.length, (row.getD k 0 : ℚ) * vals.getD k 0 := by
  induction vals generalizing row with
  | nil => simp [dot]
  | cons b bs ih =>
    cases row with
    | nil => simp [dot]
    | cons r rs =>
      simp only [dot, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      rw [ih]
      ring
private theorem bernNext_fast (st : BernState) :
    bernNext st = -(dot st.row st.vals) / ((st.vals.length : ℚ) + 1) := by
  rw [dot_eq]
  rfl
attribute [scoped cbv_eval] bernNext_fast
private theorem bernAdvance (n : Nat) (st out : BernState)
    (h : bernState n = st) (hs : bernStep st = out) : bernState (n + 1) = out := by
  change bernStep (bernState n) = out
  rw [h]
  exact hs
scoped cbv_simproc cbv_eval bernoulliSteps (bernState _) := fun e => do
  let_expr bernState n := e | return .rfl
  let some nv := Sym.getNatValue? n | return .rfl
  if nv == 0 then return .rfl
  let first := mkApp (mkConst ``bernState) (toExpr (0 : Nat))
  let res ← Lean.Meta.Tactic.Cbv.cbvEntry first
  let mut state := res.getResultExpr first
  let mut proof ← match res with
    | .step _ h .. => pure h
    | _ => Meta.mkEqRefl first
  for i in [:nv] do
    let term := mkApp (mkConst ``bernStep) state
    let res ← Lean.Meta.Tactic.Cbv.cbvEntry term
    let hp ← match res with
      | .step _ h .. => pure h
      | _ => Meta.mkEqRefl term
    let next := res.getResultExpr term
    proof ← memoProof (mkAppN (mkConst ``bernAdvance) #[toExpr i,state,next,proof,hp])
    state := next
  return .step state proof (done := true)
end Lynth.Interval.AiryProof.Kernel

namespace Lynth.Interval.AiryProof.Kernel
private theorem risingAdvance (w : Nat) (X : Ival) (n : Nat) (st out : Ival)
    (h : risingIval w X n = st)
    (hs : Ival.mul w st (Ival.add w X (Ival.ofRat w n)) = out) :
    risingIval w X (n + 1) = out := by
  change Ival.mul w (risingIval w X n) (Ival.add w X (Ival.ofRat w n)) = out
  rw [h]
  exact hs
scoped cbv_simproc cbv_eval risingSteps (risingIval _ _ _) := fun e => do
  let_expr risingIval w X n := e | return .rfl
  let some nv := Sym.getNatValue? n | return .rfl
  if nv == 0 then return .rfl
  let base := mkApp2 (mkConst ``risingIval) w X
  let first := mkApp base (toExpr (0 : Nat))
  let res ← Lean.Meta.Tactic.Cbv.cbvEntry first
  let mut state := res.getResultExpr first
  let mut proof ← match res with
    | .step _ h .. => pure h
    | _ => Meta.mkEqRefl first
  for i in [:nv] do
    let arg := mkApp2 (mkConst ``Ival.ofRat) w (toExpr (i : Rat))
    let arg := mkApp3 (mkConst ``Ival.add) w X arg
    let fn := mkLambda `v .default (mkConst ``Ival) (mkApp3 (mkConst ``Ival.mul) w (.bvar 0) arg)
    let term := mkApp fn state
    let res ← Lean.Meta.Tactic.Cbv.cbvEntry term
    let hp ← match res with
      | .step _ h .. => pure h
      | _ => Meta.mkEqRefl term
    let next := res.getResultExpr term
    proof ← memoProof (mkAppN (mkConst ``risingAdvance) #[w,X,toExpr i,state,next,proof,hp])
    state := next
  return .step state proof (done := true)
end Lynth.Interval.AiryProof.Kernel

namespace Lynth.Interval.AiryProof.Kernel
private theorem sqrtCertificate (n r : Nat)
    (hlo : decide (r * r ≤ n) = true)
    (hhi : decide (n < (r + 1) * (r + 1)) = true) : Nat.sqrt n = r := by
  have hl : r ≤ Nat.sqrt n := Nat.le_sqrt.mpr (of_decide_eq_true hlo)
  have hu : Nat.sqrt n < r + 1 := Nat.sqrt_lt.mpr (of_decide_eq_true hhi)
  omega
scoped cbv_simproc cbv_eval integerSqrt (Nat.sqrt _) := fun e => do
  let_expr Nat.sqrt n := e | return .rfl
  let some nv := Sym.getNatValue? n | return .rfl
  let r ← share (toExpr nv.sqrt)
  let tr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``Bool.true)
  let h := mkAppN (mkConst ``sqrtCertificate) #[n,r,tr,tr]
  return .step r h (done := true)
end Lynth.Interval.AiryProof.Kernel
