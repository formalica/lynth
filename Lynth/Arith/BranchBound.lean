import Lynth.Arith.Simplex

/-!
Branch-and-bound over `Simplex.solve` for integer completeness.

Z3 decides integer arithmetic by Simplex over rationals with
branch-and-bound and cuts on top (`src/math/lp`, `src/smt` arith
solvers). Our `Fourier`/`Simplex` cores are ℚ-relaxations: sound for
refutation but incomplete over `Int` (e.g. `2x = 3`). This module
closes that gap the same way Z3 does: a fractional model value `v`
for an integer variable spawns `x ≤ ⌊v⌋` / `x ≥ ⌊v⌋ + 1`, both
exhaustive over `ℤ`. Depth- and fuel-bounded; `unknown` is always a
legal answer (other procedures take over).
-/
namespace Lynth.Arith.BranchBound

open Lynth.Arith.Simplex

/-- Branch-and-bound verdict. -/
inductive BbResult where
  | sat : List Rat → BbResult
  | unsat : BbResult
  | unknown : BbResult
  deriving Repr, DecidableEq

/-- Unit-vector constraint `xⱼ ≤ b`: `(coeffs, const)` with
`coeffs[j] = 1`, `const = -b`. -/
def leBranch (j : Nat) (b : Int) (n : Nat) : List Rat × Rat :=
  ((List.range n).map (fun i => if i == j then 1 else 0), -(b : Rat))

/-- Unit-vector constraint `xⱼ ≥ b`: `-xⱼ + b ≤ 0`. -/
def geBranch (j : Nat) (b : Int) (n : Nat) : List Rat × Rat :=
  ((List.range n).map (fun i => if i == j then -1 else 0), (b : Rat))

/-- Width of a system (max constraint length). -/
def width (sys : List (List Rat × Rat)) : Nat :=
  sys.foldl (fun m (cs, _) => Nat.max m cs.length) 0

/-- First integer variable with a fractional model value, if any.
`Rat.den` is positive by normalization, so `den == 1` ⟺ integral. -/
def findFractional (model : List Rat) (intVars : List Nat) : Option (Nat × Int) :=
  intVars.find? (fun j => decide ((model.getD j 0).den != 1)) |>.map fun j =>
    let v := model.getD j 0
    (j, v.num.ediv v.den)

/-- Branch-and-bound search. `intVars` are indices constrained to `ℤ`. -/
def bb (sys : List (List Rat × Rat)) (intVars : List Nat) :
    Nat → Nat → BbResult
  | 0, _ => .unknown
  | _, 0 => .unknown
  | depth + 1, fuel + 1 =>
    match solve sys (fuel + 1) with
    | .unknown => .unknown -- Simplex out of fuel: inconclusive
    | .unsat _ => .unsat
    | .sat model =>
      match findFractional model intVars with
      | none => .sat model
      | some (j, f) =>
        let n := width sys
        let lo := bb (sys ++ [leBranch j f n]) intVars depth fuel
        match lo with
        | .unsat =>
          bb (sys ++ [geBranch j (f + 1) n]) intVars depth fuel
        | .sat m => .sat m
        | .unknown =>
          -- low branch inconclusive: high branch may still refute
          match bb (sys ++ [geBranch j (f + 1) n]) intVars depth fuel with
          | .unsat => .unknown -- only half refuted: stay inconclusive
          | other => other

end Lynth.Arith.BranchBound
