import Lynth.Arith.Simplex

/-!
DdM explanation checker: independent validation of Simplex refutations.

When `Simplex` derives UNSAT (violated basic variable, no eligible
pivot), the conflicting tableau row plus bound justifications form a
self-contained refutation: the row is re-derived from its lineage
(`combo` over the initial equations), the blocking equalities and the
violation are re-checked by evaluation, and the Farkas-style residual
constant must be positive. All checks are decidable `Bool`/`Rat`
computations — no trust in the solver's trail, only arithmetic.

This is the Simplex side of certificate validation (`Fourier.checkCert`
covers FM). The soundness theorem (`DdMExplanation` valid ⟹ system
unsatisfiable) is tracked as future work: the checker below already
encodes its exact proof obligations. See `docs/Z3-NOTES.md`.
-/
namespace Lynth.Arith.Explain

open Lynth.Arith.Simplex

/-- Static bounds: slacks `[0,∞)`, originals unbounded. -/
def boundsOf (n : Nat) (v : Nat) : Bounds :=
  if n ≤ v then { lo := some 0, hi := none } else { lo := none, hi := none }

/-- Initial-equation coefficients (`slack + originals = 0` form). -/
def initCoeff (sys : List (List Rat × Rat)) (n k p : Nat) : Rat :=
  let (cs, _) := sys.getD k ([], 0)
  if p == n + k then 1
  else if p < n then cs.getD p 0
  else 0

/-- Initial-equation constant. -/
def initConst (sys : List (List Rat × Rat)) (k : Nat) : Rat :=
  let (_, c0) := sys.getD k ([], 0)
  c0

/-- Reconstructed row coefficient from lineage. -/
def rowCoeff (sys : List (List Rat × Rat)) (n : Nat) (w : List Rat)
    (p : Nat) : Rat :=
  let m := sys.length
  (List.range m).foldl
    (fun acc k => acc + (w.getD k 0) * initCoeff sys n k p) 0

/-- Reconstructed row constant from lineage. -/
def rowConst (sys : List (List Rat × Rat)) (w : List Rat) : Rat :=
  let m := sys.length
  (List.range m).foldl
    (fun acc k => acc + (w.getD k 0) * initConst sys k) 0

/-- Assignment lookup (default 0; validated indices never miss). -/
def atBeta (beta : List Rat) (v : Nat) : Rat :=
  beta.getD v 0

/-- Validate a `DdMExplanation` against its system. -/
def checkExplanation (sys : List (List Rat × Rat))
    (e : DdMExplanation) : Bool :=
  let m := sys.length
  let n := sys.foldl (fun m (cs, _) => Nat.max m cs.length) 0
  let total := n + m
  if e.combo.length != m then false
  else if e.beta.length != total then false
  else
    -- partition: basic ++ nonbasic is exactly `range total`
    let all := e.basic ++ e.nonbasic
    if !(all.length == total && (all.all (· < total)) &&
        all.eraseDups.length == all.length) then false
    else
      let R : Nat → Rat := fun p => rowCoeff sys n e.combo p
      let Rc : Rat := rowConst sys e.combo
      -- basic form: violated var has coefficient 1, other basics 0
      if !(R e.xi == 1) then false
      else if !(e.basic.all fun v => v == e.xi || R v == 0) then false
      else
        -- reconstructed row holds under beta
        let lhs := (List.range total).foldl
          (fun acc p => acc + R p * atBeta e.beta p) 0 + Rc
        if !(lhs == 0) then false
        else if e.below then
          match (boundsOf n e.xi).lo with
          | none => false
          | some L =>
            if !(atBeta e.beta e.xi < L) then false
            else
              -- blocking: coeffs dictate the tight bound side
              let blocked := e.nonbasic.all fun j =>
                let c := R j
                if c < 0 then
                  match (boundsOf n j).hi with
                  | some u => atBeta e.beta j == u
                  | none => false
                else if 0 < c then
                  match (boundsOf n j).lo with
                  | some l => atBeta e.beta j == l
                  | none => false
                else true
              if !blocked then false
              else
                -- Farkas residual constant must be positive
                let cres := Rc +
                  (e.nonbasic.foldl (fun acc j =>
                    let c := R j
                    if c < 0 then
                      match (boundsOf n j).hi with
                      | some u => acc + c * u
                      | none => acc
                    else if 0 < c then
                      match (boundsOf n j).lo with
                      | some l => acc + c * l
                      | none => acc
                    else acc) 0) + L
                decide (0 < cres)
        else
          match (boundsOf n e.xi).hi with
          | none => false
          | some U =>
            if !(U < atBeta e.beta e.xi) then false
            else
              let blocked := e.nonbasic.all fun j =>
                let c := R j
                if 0 < c then
                  match (boundsOf n j).hi with
                  | some u => atBeta e.beta j == u
                  | none => false
                else if c < 0 then
                  match (boundsOf n j).lo with
                  | some l => atBeta e.beta j == l
                  | none => false
                else true
              if !blocked then false
              else
                let cres := (-Rc) +
                  (e.nonbasic.foldl (fun acc j =>
                    let c := R j
                    if 0 < c then
                      match (boundsOf n j).hi with
                      | some u => acc + (-c) * u
                      | none => acc
                    else if c < 0 then
                      match (boundsOf n j).lo with
                      | some l => acc + (-c) * l
                      | none => acc
                    else acc) 0) + (-U)
                decide (0 < cres)

end Lynth.Arith.Explain
