import Lynth
import Mathlib

/-! Check fixed-point enclosures against independent exact rational series.
The reference calculation rounds no terms; its geometric tail is much smaller
than one fixed-point unit. Each test has a separately measured heartbeat cap. -/

namespace IntervalArith.IntegralKernelCertificates

open Lynth.Interval (Ctx Dy Ival)
open Lynth.Interval.Integral (errorBound needsMemo prepareEval evalR)
open Intgrl (fixedTrigBounds fixedExpBounds)

private def referenceTrig (sine : Bool) (x : ℚ) (steps : Nat) : ℚ × ℚ := Id.run do
  let mut term := if sine then x else 1
  let mut sum := 0
  for k in [0:steps] do
    sum := sum+term
    let d : ℚ := if sine then (2*k+2)*(2*k+3) else (2*k+1)*(2*k+2)
    term := -term*x*x/d
  return (sum-2*|term|,sum+2*|term|)

private def referenceExp (x : ℚ) (steps : Nat) : ℚ × ℚ := Id.run do
  let mut term := 1
  let mut sum := 0
  for k in [0:steps] do
    sum := sum+term
    term := term*x/(k+1 : ℚ)
  return (sum-2*|term|,sum+2*|term|)

set_option maxHeartbeats 1164 in -- measured: 1108; +5%
run_cmd do
  for p in [1,8,64,128,384] do
    for x in [(-2 : ℚ),-1/3,0,1/17,2] do
      for sine in [true,false] do
        let (lo,hi) := fixedTrigBounds p sine x
        let (a,b) := referenceTrig sine x (p/4+16)
        let scale : ℚ := 2^p
        unless (lo : ℚ)/scale ≤ a && b ≤ (hi : ℚ)/scale do
          throwError "trigonometric enclosure failed: p={p}, sine={sine}, x={x}"

set_option maxHeartbeats 991 in -- measured: 943; +5%
run_cmd do
  for p in [1,8,64,128,384] do
    for x in [(-1/2 : ℚ),-1/3,0,1/17,1/2] do
      let (lo,hi) := fixedExpBounds p x
      let (a,b) := referenceExp x (p/4+16)
      let scale : ℚ := 2^p
      unless (lo : ℚ)/scale ≤ a && b ≤ (hi : ℚ)/scale do
        throwError "exponential enclosure failed: p={p}, x={x}"

set_option maxHeartbeats 1312 in -- measured: 1249; +5%
run_cmd do
  for p in [8,64,384] do
    let c := Ctx.make p
    for k in [1,2,3,4] do
      for n in [1,22,90,182] do
        for M in [(⟨29,-1⟩ : Dy),⟨1,-1024⟩,⟨7,1024⟩] do
          let a : Dy := ⟨-3,-3⟩
          let b : Dy := ⟨7,-2⟩
          let rho : Dy := ⟨1,k⟩
          let some bound := errorBound c n a b rho M | throwError "missing remainder"
          let r := rho.toRat
          let exactBound : ℚ := 32*(b.toRat-a.toRat)*M.toRat /
            (15*(r-1)*r^(2*n-1))
          unless exactBound ≤ bound.toRat do
            throwError "Gauss remainder underestimated: p={p}, k={k}, n={n}"

set_option maxHeartbeats 1592 in -- measured: 1516; +5%
run_cmd do
  for k in [0,1,2,31,63,64,127,255,256,1024,65535,65536,65537,70000] do
    let base := (1 : Nat) <<< k
    for n in [0,base-1,base,base+1] do
      let reference := if n == 0 then 0 else Lynth.Interval.Vendor.Dyadic.bitSearchS n 20 0
        (if (n >>> 256).beq 0 then 256 else 65536)
      unless Lynth.Interval.Vendor.Dyadic.natBitLength n == reference do
        throwError "native bit length disagrees with bounded search: k={k}"
  for k in [0,1,31,63,64,128,1024] do
    for m in [(-((2 : Int)^130)-1),-65,-1,0,1,65,(2 : Int)^130+1] do
      unless Lynth.Interval.Vendor.Dyadic.shiftLeftInt m k == m*((1 : Nat) <<< k) &&
          Lynth.Interval.Vendor.Dyadic.shiftRightInt m k == m/((1 : Nat) <<< k) do
        throwError "native signed shift disagrees with exact arithmetic: m={m}, k={k}"

set_option maxHeartbeats 1026 in -- measured: 977; +5%
run_cmd do
  let a : Intgrl.Term := .unary .exp .var
  let e : Intgrl.Term := .binary .div a (.binary .add (.rat 1) a)
  unless needsMemo e do throwError "repeated exponential was not detected"
  for p in [32,64,128] do
    let c := Ctx.make p
    let evaluate := prepareEval c e
    for x in [(-4 : ℚ),0,1/4,3] do
      for radius in [(0 : ℚ),1/1000] do
        let X := Ival.ofRats p (x-radius) (x+radius)
        let original := evalR c e X
        let cached := evaluate X
        unless original.lo.map (·.toRat) == cached.lo.map (·.toRat) &&
            original.hi.map (·.toRat) == cached.hi.map (·.toRat) do
          throwError "shared evaluation changed an enclosure: p={p}, x={x}"

end IntervalArith.IntegralKernelCertificates
