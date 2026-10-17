import Lynth.Interval.Integral.Math.FixedPoint
import Lynth.Interval.Integral.Eval
import Lynth.Interval.Core.Const

/-!
Hybrid Legendre evaluator and symmetric Gauss node generation.
The recurrence uses fixed-point integers; interval transport uses a bound
for the second derivative. High-degree evaluation switches to endpoint or
parity series and the large-degree asymptotic formula.
-/

namespace Lynth.Interval.Integral

open Intgrl Fns

def absUpper (I : Ival) : Option Dy := (Ival.abs I).hi

def atFixed (p : Nat) (x : Dy) : Int :=
  if 0 ≤ x.exponent + (p : Int) then
    x.mantissa * (2 : Int) ^ (x.exponent + p).toNat
  else x.mantissa.tdiv ((2 : Int) ^ (-(x.exponent + p)).toNat)

def fixedValue (p n : Nat) (x : Dy) : Ival × Ival :=
  let q := atFixed p x
  let (a, b) := fixedPair p q n
  let err : Dy := ⟨(2 * (n + 1) * (n + 2) : Nat), -(p : Int)⟩
  (Ival.widen p (Ival.pt ⟨a, -(p : Int)⟩) err,
   Ival.widen p (Ival.pt ⟨b, -(p : Int)⟩) err)

/-- Exact integer coefficients of 2^n P_n, in increasing parity order. -/
def zeroCoeffs (n : Nat) : Array Int := Id.run do
  let odd := n % 2
  let mut coeff : Int := (n.choose (n / 2) : Int) *
    (if odd == 0 then 1 else (n + 1 : Nat))
  if (n / 2) % 2 == 1 then coeff := -coeff
  let mut out := #[coeff]
  for j in [0:n / 2] do
    let k := 2 * j + odd
    coeff := (-coeff * (n - k : Nat) * (n + k + 1 : Nat)).tdiv
      (((k + 1) * (k + 2) : Nat) : Int)
    out := out.push coeff
  return out

def oneCoeffs (n : Nat) : Array Int := Id.run do
  let mut coeff : Int := 1
  let mut out := #[coeff]
  for k in [0:n] do
    coeff := (coeff * (n - k : Nat) * (n + k + 1 : Nat)).tdiv
      (((k + 1) ^ 2 : Nat) : Int)
    out := out.push coeff
  return out

/-- Rectangular splitting: coefficients stay exact integers, expensive
multiplications use shared powers and blocks of about sqrt(length). -/
def rectEval (p : Nat) (coeff : Array Int) (X : Ival) : Ival := Id.run do
  if coeff.isEmpty then return Ival.zero
  let block := max 1 (Nat.sqrt coeff.size)
  let mut powers := #[Ival.one]
  for _ in [0:block] do
    powers := powers.push (Ival.mul p powers.back! X)
  let mut acc := Ival.zero
  let blocks := (coeff.size + block - 1) / block
  for b in [0:blocks] do
    let k := blocks - 1 - b
    let mut v := Ival.zero
    for j in [0:block] do
      let i := k * block + j
      if i < coeff.size then
        v := Ival.add p v (Ival.mul p (Ival.pt (Dy.ofInt coeff[i]!)) powers[j]!)
    acc := Ival.add p (Ival.mul p acc powers[block]!) v
  return acc

def zeroValue (p n : Nat) (x : Dy) : Ival :=
  let P := rectEval p (zeroCoeffs n) (Ival.sq p (Ival.pt x))
  let P := if n % 2 == 1 then Ival.mul p (Ival.pt x) P else P
  Ival.mul p P (Ival.pt ⟨1, -(n : Int)⟩)

def oneValue (p n : Nat) (x : Dy) : Ival × Ival :=
  let coeff := oneCoeffs n
  let U := Ival.divNat p (Ival.sub p (Ival.pt x) Ival.one) 2
  let P := rectEval p coeff U
  let dcoeff := (coeff.extract 1 coeff.size).mapIdx fun i (a : Int) => a * ((i + 1 : Nat) : Int)
  (P, Ival.divNat p (rectEval p dcoeff U) 2)

def asympValue (c : Ctx) (n K : Nat) (x : Dy) : Ival :=
  let p := c.prec
  let X := Ival.pt x
  let S := Ival.sqrt p (Ival.sub p Ival.one (Ival.sq p X))
  let theta := Ival.sub p (Ival.divNat p c.pi 2) (asinIval c X)
  let phase := Ival.sub p
    (Ival.mul p (Ival.ofRat p ((n : ℚ) + 1 / 2)) theta) (Ival.divNat p c.pi 4)
  let phaseBox : CBox := ⟨cosIval c phase, sinIval c phase⟩
  let step : CBox := ⟨Ival.one, Ival.neg (Ival.div p X S)⟩
  let c0 := Ival.div p (Ival.pt ⟨1, (2 * n : Nat)⟩)
    (Ival.mul p (Ival.sqrt p c.pi)
      (Ival.mul p (Ival.ofRat p ((n : ℚ) + 1 / 2))
        (Ival.pt (Dy.ofNat ((2 * n).choose n)))))
  let pref := Ival.sqrt p (Ival.div p (Ival.ofRat p 2) (Ival.mul p c.pi S))
  let (v, next, _) := (List.range K).foldl (fun (acc, coeff, power) k =>
      (CBox.add p acc (CBox.mul p (CBox.ofReal coeff) power),
       Ival.mul p coeff (Ival.ofRat p
         (((2 * k + 1 : Nat) : ℚ) ^ 2 /
           (4 * (k + 1 : Nat) * (2 * n + 2 * k + 3 : Nat)))),
       CBox.mul p power step)) (CBox.ofReal Ival.zero, c0, CBox.ofReal Ival.one)
  let main := Ival.mul p pref (CBox.mul p phaseBox v).re
  let tail := Ival.mul p (Ival.ofRat p 2)
    (Ival.mul p pref (Ival.div p next (Ival.npow p S K)))
  match tail.hi with | some e => Ival.widen p main e | none => Ival.top

def pointPairNonneg (c : Ctx) (n : Nat) (x : Dy) : Ival × Ival := Id.run do
  let p := c.prec
  if n == 0 then return (Ival.one, Ival.zero)
  let X := Ival.pt x
  let D := Ival.sub p Ival.one (Ival.sq p X)
  if Dy.ltB (Dy.ofRatD 64 (49/50)) x then return oneValue (p + 2 * n + 16) n x
  let (prev, val) :=
    if n > 256 && p < n / 2 then
      let K := min n (p / 2 + 12)
      let v := asympValue c n K x
      let a := asympValue c (n - 1) K x
      (a, v)
    else if p > 1024 || Dy.ltB x (Dy.ofRatD 64 (1/20)) then
      let w := p + 2 * n + 16
      (zeroValue w (n - 1) x, zeroValue w n x)
    else
      fixedValue (p + 2 * (Nat.log2 (n + 2)) + 16) n x
  return (val, Ival.div p
    (Ival.mul p (Ival.ofRat p n) (Ival.sub p prev (Ival.mul p X val))) D)

def pointPair (c : Ctx) (n : Nat) (x : Dy) : Ival × Ival :=
  if x.mantissa < 0 then
    let (v,d) := pointPairNonneg c n x.neg
    (if n % 2 == 1 then Ival.neg v else v,
     if n % 2 == 0 then Ival.neg d else d)
  else pointPairNonneg c n x

/-- Global second-derivative bound. The interior bound is selected when tighter. -/
def secondBound (p n : Nat) (X : Ival) : Ival :=
  let global := Ival.ofRat p
    (((n - 1 : Nat) : ℚ) * n * (n + 1) * (n + 2) / 8)
  let D := Ival.sub p Ival.one (Ival.sq p X)
  if D.pos then
    let inner := Ival.div p
      (Ival.mul p (Ival.ofRat p ((13 : ℚ) * n / 4)) (Ival.sqrt p (Ival.ofRat p n)))
      (Ival.mul p D (Ival.sqrt p (Ival.sqrt p D)))
    Ival.min global inner
  else global

def onInterval (c : Ctx) (n : Nat) (X : Ival) : Ival × Ival :=
  match X.mid, X.lo, X.hi with
  | some m, some a, some b =>
    let (v, d) := pointPair c n m
    let radius := Dy.max (Dy.subU c.prec m a) (Dy.subU c.prec b m)
    let e := Ival.mul c.prec (secondBound c.prec n X) (Ival.pt radius)
    let d := match e.hi with | some t => Ival.widen c.prec d t | none => Ival.top
    let ferror := Ival.mul c.prec (Ival.abs d) (Ival.pt radius)
    let v := match ferror.hi with | some t => Ival.widen c.prec v t | none => Ival.top
    (v, d)
  | _, _, _ => (Ival.top, Ival.top)

def gaussWeightI (c : Ctx) (n : Nat) (X : Ival) : Ival :=
  let d := (onInterval c n X).2
  Ival.div c.prec (Ival.ofRat c.prec 2)
    (Ival.mul c.prec (Ival.sub c.prec Ival.one (Ival.sq c.prec X)) (Ival.sq c.prec d))

structure NodeTable where
  roots : List (Dy × Dy)
  certWeights : List Ival := []
deriving Repr, Inhabited

def rootIval (r : Dy × Dy) : Ival := ⟨some r.1, some r.2⟩

def rootSignCheck (c : Ctx) (n : Nat) (r : Dy × Dy) : Bool :=
  Dy.ltB r.1 r.2 && Dy.ltB (Dy.ofInt (-1)) r.1 && Dy.ltB r.2 Dy.one &&
    (Ival.mul c.prec (pointPair c n r.1).1 (pointPair c n r.2).1).negv

def rawDyEq (a b : Dy) : Bool :=
  a.mantissa == b.mantissa && a.exponent == b.exponent

def reflectedRoots (rs : List (Dy × Dy)) : List (Dy × Dy) :=
  rs.reverse.map (fun (a,b) => (b.neg,a.neg))

def NodeTable.computeWeights (c : Ctx) (t : NodeTable) : List Ival :=
  if t.roots.length == 1 then [Ival.ofRat c.prec 2]
  else
    let right := (t.roots.drop (t.roots.length/2)).map
      (fun r => gaussWeightI c t.roots.length (rootIval r))
    right.reverse ++ right

def rawEndpointEq : Option Dy → Option Dy → Bool
  | none, none => true
  | some a, some b => rawDyEq a b
  | _, _ => false

def rawIvalEq (a b : Ival) : Bool :=
  rawEndpointEq a.lo b.lo && rawEndpointEq a.hi b.hi

def NodeTable.weights (_c : Ctx) (t : NodeTable) : List Ival := t.certWeights

def NodeTable.check (c : Ctx) (t : NodeTable) : Bool :=
  let n := t.roots.length
  let rootsOK := if n == 1 then
    match t.roots with
    | [(a,b)] => a.isZero && b.isZero
    | _ => false
  else
    let right := t.roots.drop (n/2)
    n > 0 && n % 2 == 0 &&
    ((t.roots.take (n/2)).zip (reflectedRoots right)).all
      (fun (a,b) => rawDyEq a.1 b.1 && rawDyEq a.2 b.2) &&
    right.all (rootSignCheck c n) &&
    (t.roots.zip t.roots.tail).all (fun (a,b) => Dy.ltB a.2 b.1)
  rootsOK && t.certWeights.length == n &&
    ((t.computeWeights c).zip t.certWeights).all (fun (a,b) => rawIvalEq a b)

/-- Only untrusted guesses use Float. Every returned table must pass check. -/
def generateNodes (c : Ctx) (n : Nat) : Option NodeTable := Id.run do
  if n == 1 then return some ⟨[(Dy.zero,Dy.zero)], [Ival.ofRat c.prec 2]⟩
  if n == 0 || n % 2 != 0 then return none
  let mut positive : List (Dy × Dy) := []
  for k in [0:n/2] do
    let seed := Float.cos (3.141592653589793 * ((k.toFloat + 0.75) / (n.toFloat + 0.5)))
    let mant := (seed * 1099511627776.0).toUInt64.toNat
    let mut X := Ival.widen c.prec (Ival.pt ⟨mant, -40⟩) ⟨1,-28⟩
    let mut work := 48
    for iteration in [0:24] do
      let cc : Ctx := {c with prec := min (c.prec + 24) work}
      let some m := X.mid | return none
      let (v, dp) := pointPair cc n m
      let (some xa, some xb) := (X.lo,X.hi) | return none
      let radius := Dy.max (Dy.subU cc.prec m xa) (Dy.subU cc.prec xb m)
      let de := Ival.mul cc.prec (secondBound cc.prec n X) (Ival.pt radius)
      let some er := de.hi | return none
      let d := Ival.widen cc.prec dp er
      let Y := Ival.sub cc.prec (Ival.pt m) (Ival.div cc.prec v d)
      if !Y.isFinite then return none
      let (some a, some b) := (Y.lo,Y.hi) | return none
      X := Ival.widen cc.prec Y (Dy.max ⟨1,-(cc.prec : Int) + 8⟩
        (Dy.subU cc.prec b a))
      if iteration ≥ 6 && work ≥ c.prec + 24 then break
      if iteration ≥ 5 then work := work * 2
    -- Leave room for the independent sign check at the requested precision.
    -- Refinement used guard precision; an excessively narrow bracket can
    -- otherwise be smaller than the checker's evaluation uncertainty.
    X := Ival.widen c.prec X ⟨1, -(c.prec : Int) + 4⟩
    let (some a, some b) := (X.lo,X.hi) | return none
    positive := positive ++ [(a,b)]
  let negative := positive.map (fun (a,b) => (b.neg,a.neg))
  let t : NodeTable := ⟨negative ++ positive.reverse, []⟩
  return some {t with certWeights := t.computeWeights c}

end Lynth.Interval.Integral
