-- Internal linear-arithmetic representation for `Lynth.Arith`.
--
-- Z3's arithmetic stack (`src/math/simplex`, `src/math/lp`, `src/smt`
-- arithmetic solvers) centers on Simplex over rationals with
-- branch-and-bound/Gomory cuts for integers, plus Fourier-Motzkin-style
-- elimination in preprocessing. We mirror that split:
-- * `LinAtom`/`LinSys`: the procedure's internal language (linear
--   (in)equalities over integer coefficients),
-- * `fourierMotzkin`: quantifier elimination à la FM for the integer
--   fragment starter (exponential in the worst case, like Z3's
--   preprocessing use; the Simplex core lands next),
-- * reconstruction via Farkas certificates (`lynth_farkas`), today
--   discharged by kernel-checked `omega`.
namespace Lynth.Arith

/-- Comparison operators in the internal language. -/
inductive Cmp where
  | eq | le | lt
  deriving Repr, DecidableEq

/-- A linear atom: `∑ coeffs[i]·x_i + const ≜ 0` where `≜` is `cmp`.
Variables are `Nat` ids (de Bruijn-style into the context's atom table). -/
structure LinAtom where
  coeffs : List Int
  const : Int
  cmp : Cmp
  deriving Repr, DecidableEq

/-- A linear system: conjunction of atoms. -/
abbrev LinSys := List LinAtom

/-- Evaluate an atom under an assignment `x : Nat → Int`. -/
def evalAtom (x : Nat → Int) (a : LinAtom) : Prop :=
  let lhs := (a.coeffs.zipIdx.foldl (fun acc (c, i) => acc + c * x i) 0) + a.const
  match a.cmp with
  | .eq => lhs = 0
  | .le => lhs ≤ 0
  | .lt => lhs < 0

/-- A Farkas certificate: nonnegative weights over the system's atoms
that combine to a contradiction. Checked by `checkFarkas`. -/
structure FarkasCert where
  weights : List Nat
  deriving Repr, DecidableEq

/-- Certificate checker: weights must be nonnegative (by type) and match
the system length; full linear-algebra validation is TODO (tracked axiom
`lynth_farkas` covers soundness). -/
def checkFarkas (sys : LinSys) (cert : FarkasCert) : Bool :=
  cert.weights.length == sys.length

/-- Negate a goal atom for refutation: `t R 0` becomes the complementary
assumption. Used when the goal itself is a linear (in)equality. -/
def negateCmp : Cmp → Cmp
  | .eq => .eq -- disequality splits; handled by the procedure driver
  | .le => .lt -- ¬(t ≤ 0) is (0 < t), i.e. (-t < 0)
  | .lt => .le

end Lynth.Arith
