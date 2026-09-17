import Lynth.Sat.Solver
import Lynth.Certificates

/-!
Proof reconstruction for `Lynth.Sat`: checking certificates.

Today the checker validates SAT certificates (`checkSat`); UNSAT
certificates (resolution traces / DRAT, cf. Z3's `sat_drat.cpp`) are
represented as opaque `Nat` ids until the trace checker lands.
Soundness of applying a checked certificate is `Lynth.lynth_sat_resolve`.
-/
namespace Lynth.Sat.Reconstruct

/-- Check a SAT certificate: the assignment must satisfy the CNF. -/
def checkSatCert (cnf : CNF) (a : Assignment) : Bool :=
  checkSat cnf a

/-- Opaque UNSAT certificate (resolution-trace id). -/
structure UnsatCert where
  traceId : Nat
  deriving Repr, DecidableEq

/-- Placeholder UNSAT checker: accepts any trace id for now.
TODO: real resolution-trace validation against the input CNF. -/
def checkUnsatCert (_cnf : CNF) (_cert : UnsatCert) : Bool :=
  true

end Lynth.Sat.Reconstruct
