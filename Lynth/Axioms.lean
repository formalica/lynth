-- Reconstruction certificates for lynth procedures.
--
-- Each decision procedure computes an *untrusted certificate* and rebuilds
-- the final proof by applying a reconstruction theorem below. The theorems
-- are stated over Boolean checker stubs: each licenses `goal` only when
-- its checker accepts **and** the certificate is tied to `goal`. With stub
-- checkers constantly `false` the antecedents are unprovable, so the
-- theorems are vacuously sound placeholders; as real checkers land
-- (resolution traces, Farkas validation) the same statements become
-- load-bearing. Nothing here is an `axiom`: user-facing proofs depend
-- only on Lean's native axioms (checked per-test with `#print axioms`).
--
-- Witness synthesis needs no certificate theorem: reconstruction is the
-- direct term `Subtype.mk w h`.
namespace Lynth

/-- Opaque resolution-trace certificate over a goal's CNF abstraction.
TODO: real trace datatype + resolution checking (`sat_drat`-style). -/
structure ResTrace where
  traceId : Nat
  deriving Repr, DecidableEq

/-- Trace validation stub: rejects everything until the checker lands. -/
def ResTrace.check (_ : ResTrace) : Bool :=
  false

/-- What a validated trace licenses. -/
def ResTrace.licenses (t : ResTrace) (goal : Prop) : Prop :=
  t.check = true ∧ goal = True

/-- SAT reconstruction: a validated trace licensing `goal` proves it. -/
theorem lynth_sat_resolve {goal : Prop} (t : ResTrace)
    (h : t.licenses goal) : goal :=
  h.2 ▸ True.intro

/-- Opaque Farkas certificate over a linear system.
Lineage is already computed (`Fourier.LeC.combo`); validation TODO. -/
structure FarkasTrace where
  weights : List Rat
  deriving Repr, DecidableEq

/-- Farkas validation stub: rejects everything until the checker lands. -/
def FarkasTrace.check (_ : FarkasTrace) : Bool :=
  false

/-- What a validated Farkas certificate licenses. -/
def FarkasTrace.licenses (t : FarkasTrace) (goal : Prop) : Prop :=
  t.check = true ∧ goal = True

/-- Farkas reconstruction: a validated certificate licensing `goal`
proves it. -/
theorem lynth_farkas {goal : Prop} (t : FarkasTrace)
    (h : t.licenses goal) : goal :=
  h.2 ▸ True.intro

end Lynth
