

/-!
Fourier–Motzkin elimination over a rational relaxation.

Z3's arithmetic stack centers on Simplex over rationals
(`src/math/simplex`, `src/math/lp`) with branch-and-bound/cuts for
integers. This module is the elimination core we start from: linear
`≤` systems over `Rat` (a sound relaxation of `Int`/`Nat` for
*refutation*: ℚ-UNSAT ⟹ ℤ-UNSAT), with full combination lineage so
every derived constraint carries its Farkas certificate over the
original atoms (`combo` weights feed `lynth_farkas` later).
-/
namespace Lynth.Arith.Fourier

/-- A `≤` constraint `∑ coeffs[i]·xᵢ + const ≤ 0` with lineage `combo`
(weights over the original system, same length for every constraint). -/
structure LeC where
  coeffs : List Rat
  const : Rat
  combo : List Rat
  deriving Repr, DecidableEq, Inhabited

/-- Coefficient lookup with zero default. -/
def coeffAt (c : LeC) (j : Nat) : Rat :=
  c.coeffs.getD j 0

/-- Pad a coefficient list to length `n`. -/
def pad (n : Nat) (l : List Rat) : List Rat :=
  l ++ List.replicate (n - l.length) 0

/-- Number of variables (max constraint width). -/
def nVars (sys : List LeC) : Nat :=
  sys.foldl (fun m c => Nat.max m c.coeffs.length) 0

/-- Make a constraint over `nOrig` originals with unit lineage `k`. -/
def mkLe (coeffs : List Rat) (const : Rat) (nOrig k : Nat) : LeC :=
  { coeffs, const,
    combo := List.range nOrig |>.map fun i => if i == k then 1 else 0 }

/-- Combine an upper bound `u` (`coeff > 0` at `j`) with a lower bound `l`
(`coeff < 0` at `j`): positive combination killing `xⱼ`. Sound: the
result follows from `u ≤ 0`, `l ≤ 0` by nonnegative combination. -/
def combine (u l : LeC) (j n nOrig : Nat) : LeC :=
  let au := coeffAt u j
  let al := -(coeffAt l j)
  let uc := pad n u.coeffs
  let lc := pad n l.coeffs
  let cc := List.zipWith (fun a b => a / au + b / al) uc lc
  let cu := pad nOrig u.combo
  let cl := pad nOrig l.combo
  let cb := List.zipWith (fun a b => a / au + b / al) cu cl
  { coeffs := cc, const := u.const / au + l.const / al, combo := cb }

/-- A constraint is an explicit contradiction if it reads `c ≤ 0`, `c > 0`. -/
def isContra (c : LeC) : Bool :=
  c.coeffs.all (· == 0) && decide (0 < c.const)

/-- One elimination step on variable `j`: immediate-contradiction check,
then FM combination. `Except` carries the Farkas certificate on the
error channel. -/
def step (sys : List LeC) (j : Nat) : Except (List Rat) (List LeC) :=
  match sys.find? isContra with
  | some c => Except.error c.combo
  | none =>
    let n :=
      sys.foldl (fun m c => Nat.max m (Nat.max c.coeffs.length c.combo.length)) 0
    let nOrig := sys.foldl (fun m c => Nat.max m c.combo.length) 0
    let (pos, rest) := sys.partition fun c => decide (0 < coeffAt c j)
    let (neg, zero) := rest.partition fun c => decide (coeffAt c j < 0)
    let derived := pos.flatMap fun u => neg.map fun l => combine u l j n nOrig
    match derived.find? isContra with
    | some c => Except.error c.combo
    | none => Except.ok (zero ++ derived)

/-- Eliminate `n` variables starting at `j`, fuel-bounded.
Returns the Farkas certificate on refutation, `none` otherwise
(relaxation is incomplete for integers: SAT here is inconclusive). -/
def solve (sys : List LeC) (fuel : Nat := 128) : Option (List Rat) :=
  let n := nVars sys
  match go sys fuel 0 (n + 1) with
  | .error cert => some cert
  | .ok _ => none
where
  go : List LeC → Nat → Nat → Nat → Except (List Rat) Unit
    | _, 0, _, _ => Except.ok ()
    | _, _, _, 0 => Except.ok ()
    | s, f + 1, j, k + 1 =>
      match step s j with
      | .error cert => Except.error cert
      | .ok s' => go s' f (j + 1) k

end Lynth.Arith.Fourier
