import Lynth.Interval.Integral.Math.NestedSubstitution
import Lynth.Interval.Integral.Engine

/-! Scoped expression operations, exact memo keys, and elementary rewrites.
The legacy univariate syntax and its proof obligations are unchanged. -/
namespace Lynth.Interval.Integral.Nested
open Intgrl

abbrev Expr := NExpr

def _root_.Intgrl.NExpr.size : Expr → Nat
  | .var _ | .rat _ | .pi => 1
  | .unary _ a | .pow a _ | .rpow a _ => a.size+1
  | .binary _ a b => a.size+b.size+1
  | .integral _ a b f => a.size+b.size+f.size+1

def _root_.Intgrl.NExpr.uses (i : Nat) : Expr → Bool
  | .var j => i == j
  | .rat _ | .pi => false
  | .unary _ a | .pow a _ | .rpow a _ => a.uses i
  | .binary _ a b => a.uses i || b.uses i
  | .integral _ a b f => a.uses i || b.uses i || f.uses i

def _root_.Intgrl.NExpr.hasIntegral : Expr → Bool
  | .integral .. => true
  | .unary _ a | .pow a _ | .rpow a _ => a.hasIntegral
  | .binary _ a b => a.hasIntegral || b.hasIntegral
  | _ => false

/-- Small exact simplifications also expose endpoint cancellations. -/
def add (a b : Expr) : Expr :=
  match a,b with
  | .rat 0,b => b | a,.rat 0 => a
  | .rat p,.rat q => .rat (p+q)
  | _,_ => .binary .add a b

def neg (a : Expr) : Expr :=
  match a with | .rat q => .rat (-q) | .unary .neg a => a | _ => .unary .neg a

def sub (a b : Expr) : Expr :=
  if a == b && !a.hasIntegral then .rat 0 else
  match a,b with
  | a,.rat 0 => a | .rat p,.rat q => .rat (p-q)
  | a,.binary .sub b c => if a == b && !a.hasIntegral then c else .binary .sub a (.binary .sub b c)
  | .binary .sub a b,c =>
    if a == c && !a.hasIntegral then neg b else .binary .sub (.binary .sub a b) c
  | .binary .add a b,c => if a == c && !a.hasIntegral then b else if b == c && !b.hasIntegral then a else .binary .sub (.binary .add a b) c
  | _,_ => .binary .sub a b

def mul (a b : Expr) : Expr :=
  match a,b with
  | .rat 0,b => if b.hasIntegral then .binary .mul a b else .rat 0
  | a,.rat 0 => if a.hasIntegral then .binary .mul a b else .rat 0
  | .rat 1,b => b | a,.rat 1 => a
  | .rat p,.rat q => .rat (p*q)
  | _,_ => .binary .mul a b

def div (a b : Expr) : Expr :=
  match a,b with
  | a,.rat 1 => a
  | .rat p,.rat q => .rat (p/q)
  | _,_ => .binary .div a b

def pow (a : Expr) (n : Nat) : Expr :=
  if n == 0 && !a.hasIntegral then .rat 1 else if n == 1 then a else
  match a with
  | .unary .neg a => if n % 2 == 0 then .pow a n else neg (.pow a n)
  | _ => .pow a n

def rpow (a : Expr) (q : ℚ) : Expr :=
  if q == 0 && !a.hasIntegral then .rat 1 else if q == 1 then a else
  if q.den == 1 && q.num ≥ 0 then pow a q.num.toNat else .rpow a q

def simplify : Expr → Expr
  | .unary .neg a => neg (simplify a)
  | .unary op a => .unary op (simplify a)
  | .binary .add a b => add (simplify a) (simplify b)
  | .binary .sub a b => sub (simplify a) (simplify b)
  | .binary .mul a b => mul (simplify a) (simplify b)
  | .binary .div a b => div (simplify a) (simplify b)
  | .binary op a b => .binary op (simplify a) (simplify b)
  | .pow a n => pow (simplify a) n
  | .rpow a q => rpow (simplify a) q
  | .integral k a b f => .integral k (simplify a) (simplify b) (simplify f)
  | e => e

/-- Pull powers of the positive integration variable out of arithmetic.
Used only after a change of variables on (0,1); endpoint values are null.
This exposes cancellations such as 2*t/sqrt(t^2) before interval evaluation. -/
def collectPower (level : Nat) : Expr → ℚ × Expr
  | .var i => if i == level then (1,.rat 1) else (0,.var i)
  | .binary op a b =>
    let (p,A) := collectPower level a
    let (q,B) := collectPower level b
    match op with
    | .mul => (p+q,mul A B)
    | .div => (p-q,div A B)
    | .add | .sub =>
      let r := min p q
      let a := mul (rpow (.var level) (p-r)) A
      let b := mul (rpow (.var level) (q-r)) B
      (r,if op == .add then add a b else sub a b)
    | _ => (0,.binary op a b)
  | .unary .neg a => let (p,A) := collectPower level a; (p,neg A)
  | .unary .inv a => let (p,A) := collectPower level a; (-p,.unary .inv A)
  | .unary .sqrt a => let (p,A) := collectPower level a; (p/2,.unary .sqrt A)
  | .pow a n => let (p,A) := collectPower level a; (p*n,pow A n)
  | e => (0,e)

def regularize (level : Nat) (e : Expr) : Expr :=
  let (p,A) := collectPower level (simplify e)
  simplify (mul (rpow (.var level) p) A)

/-- Transformations are verified again during replay; no transformed value
is inserted by the expression compiler. -/
inductive Change where
  | identity | affine | right | left
  | power (degree : Nat) (fromRight : Bool)
  deriving Repr, BEq, Inhabited

def transformed (n : Nat) (how : Change) (a b f : Expr) : Expr :=
  let t := NExpr.var n
  match how with
  | .identity => f
  | .affine | .power .. =>
    let A := a.shift n 1
    let B := b.shift n 1
    let w := sub B A
    let E := simplify (mul w (f.replace n (add A (mul w t))))
    match how with
    | .power m right =>
      let u := pow t m
      let mapped := if right then sub (.rat 1) u else u
      regularize n (mul (mul (.rat m) (pow t (m-1))) (E.replace n mapped))
    | _ => E
  | .right | .left =>
    let d := sub (.rat 1) t
    -- Stable Mobius evaluation: Re(1/(1-z)) stays positive on a
    -- right half-plane. Evaluating z/(1-z) directly loses this dependency.
    let u := sub (.unary .inv d) (.rat 1)
    let A := a.shift n 1
    let y := if how == .right then add A u else sub A u
    let E := simplify (div (f.replace n y) (pow d 2))
    let atRight := simplify (E.replace n (sub (.rat 1) t))
    simplify ((regularize n atRight).replace n (sub (.rat 1) t))

/-- Standalone tail/endpoint identities. A returned guard must be checked
on the complete real parameter domain before the formula can be used. -/
structure Formula where
  value : Expr
  nonnegative : Option Expr := none
  positive : Option Expr := none
  deriving Repr, Inhabited

def powerKernel (n : Nat) (base : Expr) : Expr → Option ℚ
  | .pow a k => if a == base then some k else none
  | .rpow a q => if a == base then some q else none
  | .unary .sqrt a => if a == base then some (1/2) else none
  | .unary .inv (.unary .sqrt a) => if a == base then some (-1/2) else none
  | .binary .div (.rat q) (.unary .sqrt a) => if q == 1 && a == base then some (-1/2) else none
  | .unary .inv a => if a == base then some (-1) else none
  | .binary .div (.rat q) (.pow a k) => if q == 1 && a == base then some (-(k : ℚ)) else none
  | .binary .div (.rat q) a => if q == 1 && a == base then some (-1) else none
  | .var i => if base == .var i && i == n then some 1 else none
  | _ => none

def formula (n : Nat) (kind : NDomain) (a b f : Expr) : Option Formula := do
  let y := NExpr.var n
  if kind == .right then
    if f == .unary .exp (neg y) then return ⟨.unary .exp (neg a),none,none⟩
    match f with
    | .unary .exp (.binary .sub c y') =>
      if y' == y && !c.uses n && !c.hasIntegral then return ⟨.unary .exp (sub c a),none,none⟩
    | _ => pure ()
    return ← none
  if kind == .left then
    if f == .unary .exp y then return ⟨.unary .exp a,none,none⟩
    match f with
    | .unary .exp (.binary .add c y') =>
      if y' == y && !c.uses n && !c.hasIntegral then
        return ⟨.unary .exp (add c a),none,none⟩
    | .unary .exp (.binary .sub y' c) =>
      if y' == y && !c.uses n && !c.hasIntegral then
        return ⟨.unary .exp (sub a c),none,none⟩
    | _ => pure ()
    return ← none
  if !kind.finite then return ← none
  let width := sub b a
  if a == .rat 0 && f == .unary .log y then
    return ⟨mul b (sub (.unary .log b) (.rat 1)),some b,none⟩
  if a == .rat 0 && f == neg (.unary .log y) then
    return ⟨mul b (sub (.rat 1) (.unary .log b)),some b,none⟩
  let q ← (if a == .rat 0 then powerKernel n y f else none)
    <|> powerKernel n (sub y a) f <|> powerKernel n (sub b y) f
  if q ≤ -1 then none else
    some ⟨div (rpow width (q+1)) (.rat (q+1)),some width,none⟩

def uCode : Unary → Nat
  | .neg => 0 | .inv => 1 | .exp => 2 | .sin => 3 | .cos => 4 | .sinh => 5
  | .cosh => 6 | .log => 7 | .sqrt => 8 | .abs => 9 | .floor => 10 | .atan => 11

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

/-- A whole-line split follows a visible translation, when present. This
avoids repeatedly bounding a shifted Gaussian on unrelated half-lines. -/
def center (level : Nat) : Expr → Expr
  | .binary .sub (.var i) a =>
    if i == level && !a.uses level && !a.hasIntegral then a else .rat 0
  | .unary _ a | .pow a _ | .rpow a _ => center level a
  | .binary _ a b =>
    let c := center level a
    if c == .rat 0 then center level b else c
  | _ => .rat 0

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
