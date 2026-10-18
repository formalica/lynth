import Lynth.Interval.Integral.Math.NestedSyntax
import Lynth.Interval.Integral.Engine

/-! Scoped expression operations, exact memo keys, and elementary rewrites.
The legacy univariate syntax and its proof obligations are unchanged. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

def uCode : Unary → Nat
  | .neg => 0 | .inv => 1 | .exp => 2 | .sin => 3 | .cos => 4 | .sinh => 5
  | .cosh => 6 | .log => 7 | .sqrt => 8 | .abs => 9 | .floor => 10 | .atan => 11
  | .erf => 12 | .si => 13 | .eta => 14 | .airyAi => 15

def bCode : Binary → Nat
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .max => 4 | .min => 5

def dCode : NDomain → Nat
  | .interval => 0 | .icc => 1 | .ioc => 2 | .ico => 3 | .ioo => 4
  | .right => 5 | .left => 6 | .whole => 7

/-- Unlike Lean's opaque mixHash, this mixer reduces in the kernel too. -/
def combineHash (a b : UInt64) : UInt64 :=
  let z := (a ^^^ b) * 0x9e3779b185ebca87
  z ^^^ (z >>> 32)

instance : Hashable Expr where
  hash := fun e => go e
where
  go : Expr → UInt64
    | .var i => combineHash 1 (hash i)
    | .rat q => combineHash 2 (combineHash (hash q.num) (hash q.den))
    | .pi => 3
    | .unary op a => combineHash (combineHash 4 (hash (uCode op))) (go a)
    | .binary op a b => combineHash (combineHash 5 (hash (bCode op))) (combineHash (go a) (go b))
    | .pow a n => combineHash 6 (combineHash (go a) (hash n))
    | .rpow a q => combineHash 7 (combineHash (go a) (combineHash (hash q.num) (hash q.den)))
    | .integral k a b f => combineHash (combineHash 8 (hash (dCode k))) (combineHash (go a) (combineHash (go b) (go f)))

def sameDy (a b : Dy) : Bool := a.mantissa == b.mantissa && a.exponent == b.exponent

def sameIval (a b : Ival) : Bool :=
  let eq := fun x y => match x,y with
    | none,none => true | some a,some b => sameDy a b | _,_ => false
  eq a.lo b.lo && eq a.hi b.hi

def hashIval (a : Ival) : UInt64 :=
  let h := fun x => match x with
    | none => 0 | some a => combineHash (hash a.mantissa) (hash a.exponent)
  combineHash (h a.lo) (h a.hi)

structure Key where
  expr : Expr
  env : Array Ival
  deriving Inhabited

instance : BEq Key where
  beq a b := a.expr == b.expr && a.env.size == b.env.size &&
    (a.env.zip b.env).all (fun (x,y) => sameIval x y)
instance : Hashable Key where
  hash k := k.env.foldl (fun h x => combineHash h (hashIval x)) (hash k.expr)

/-- Canonical half-line transforms also erase irrelevant translations from
memo keys. Every cached result is still checked against its original source. -/
def key (e : Expr) (env : Array Ival) : Key :=
  let normalized := match e with
    | .integral .right a b f =>
      if a.hasIntegral || b.hasIntegral then e else
        NExpr.integral .interval (.rat 0) (.rat 1) (transformed env.size .right a b f)
    | .integral .left a b f =>
      if a.hasIntegral || b.hasIntegral then e else
        NExpr.integral .interval (.rat 0) (.rat 1) (transformed env.size .left a b f)
    | _ => e
  ⟨normalized,env.mapIdx fun i v => if normalized.uses i then v else Ival.zero⟩

/-- A small resizing table with Nat indices. Std.HashMap uses machine-word
indexing whose reduction is unsuitable for kernel certificate replay. The
same pure lookup/insert functions are used by search and by the checker. -/
structure Memo where
  buckets : Array (List (Key × Ival)) := #[]
  count : Nat := 0
  deriving Inhabited

def Memo.find? (m : Memo) (k : Key) : Option Ival := do
  if m.buckets.isEmpty then none else do
    let bucket := m.buckets[(hash k).toNat % m.buckets.size]!
    let (_,v) ← bucket.find? (fun (a,_) => a == k)
    return v

instance : GetElem? Memo Key Ival (fun m k => (m.find? k).isSome) where
  getElem m k h := (m.find? k).get h
  getElem? := Memo.find?

def Memo.isEmpty (m : Memo) : Bool := m.count == 0

private def putBucket (bs : Array (List (Key × Ival))) (k : Key) (v : Ival) :=
  let i := (hash k).toNat % bs.size
  bs.set! i ((k,v) :: bs[i]!)

def Memo.insert (m : Memo) (k : Key) (v : Ival) : Memo := Id.run do
  let mut bs := if m.buckets.isEmpty then Array.replicate 16 [] else m.buckets
  if m.count ≥ 2*bs.size then
    bs := bs.foldl (fun out bucket => bucket.reverse.foldl
      (fun out (key,value) => putBucket out key value) out)
      (Array.replicate (2*bs.size) [])
  return ⟨putBucket bs k v,m.count+1⟩

end Lynth.Interval.Integral.Nested
