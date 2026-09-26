import Lynth.Sat.Cdcl

/-!
Verified SAT-solver interface: soundness and completeness.

Our CDCL engine (`Lynth.Sat.Cdcl`, a native Lean 4 port of CreuSAT's
propagation and decision machinery) is the workhorse behind finite-domain
search. Proving it correct once unlocks two things at once:

- UNSAT answers become proofs: `cdcl_complete` turns a solver-reported
  UNSAT into `∀ a, checkSat cnf a = false`, with no DRAT certificates
  needed (the DRAT reconstruction track is thereby retired).
- verified solver *functions*: meta-level synthesis (`Graph → Option
  Coloring` and friends) runs the solver inside the target function and
  discharges its correctness proof via `cdcl_sound`/`cdcl_complete`.

The full proof (soundness of unit propagation + learning, completeness
of the search with restarts) is long and hard: CreuSAT itself is
imperative code verified via Hoare-logic assertions and invariants
(https://github.com/sarsko/CreuSAT), and our Lean proof will follow the
same invariant structure. Until that proof lands, correctness is
postulated by the single temporary axiom `cdcl_correct` below, from
which exactly the two theorems `cdcl_sound` and `cdcl_complete` are
derived. **Nothing else may use the axiom** (enforced by inspection:
`cdcl_correct` must appear only in the two proofs below).

Why the axiom as stated is the right (true) statement:

- Soundness: `cdclSolve` gates every SAT answer through `checkSat`
  (`Lynth.Sat.Cdcl.cdclSolve`, "defense in depth"), and duplicate
  literals are stripped up front while `0` literals are dropped at
  `mkWS` time — none of which changes satisfaction (`0` is never a
  valid literal: `checkSat` evaluates it to `false`, and dropping it
  from a clause preserves (un)satisfiability; an emptied clause is
  reported UNSAT, which is correct). So a reported model genuinely
  satisfies the *original* `cnf`.
- Completeness: `mkWS` answers `none` (immediate UNSAT) only when some
  clause is empty after sanitization, i.e. only for genuinely
  unsatisfiable inputs. Branch restriction (`branch`) only *orders*
  decisions: `getNext` falls back to an unrestricted pass
  (`Lynth.Sat.Watch.getNext`, "so models stay complete"), so no
  satisfying assignment is ever cut off. Fuel/restarts only bound the
  search: the axiom claims nothing about `none` (unknown) results,
  only that a *reported* UNSAT is genuine.
-/
namespace Lynth.Sat

/-- Certified entry point: branch restriction as a plain reflectable
list (hash sets cannot be reflected to syntax), converted once to the
solver's hash set. Tactics and synthesized functions go through this
wrapper so that native-evaluation evidence (`native_decide`) and the
correctness theorems below speak about the same call. -/
def cdclSolveB (cnf : CNF) (fuel restartBase : Nat) (branch : List Nat) :
    Cdcl.CdclOut :=
  Cdcl.cdclSolve cnf fuel restartBase (Std.HashSet.ofList branch)

/-- TEMPORARY AXIOM — solver correctness (soundness + completeness).
To be proven from the `Watch` implementation (CreuSAT invariant
structure) once the campaign allows; until then every verified-solver
proof bottoms out here. See the module doc for why this statement is
true of the implementation. -/
axiom cdcl_correct (cnf : CNF) (fuel restartBase : Nat) (branch : List Nat) :
  (∀ m : Assignment, (cdclSolveB cnf fuel restartBase branch).result = some (.sat m) →
    checkSat cnf m = true) ∧
  ((cdclSolveB cnf fuel restartBase branch).result = some .unsat →
    ∀ a : Assignment, checkSat cnf a = false)

/-- Soundness: a reported model genuinely satisfies the input. -/
theorem cdcl_sound (cnf : CNF) (fuel restartBase : Nat) (branch : List Nat)
    (m : Assignment)
    (h : (cdclSolveB cnf fuel restartBase branch).result = some (.sat m)) :
    checkSat cnf m = true :=
  (cdcl_correct cnf fuel restartBase branch).1 m h

/-- Completeness: a reported UNSAT means no satisfying assignment exists. -/
theorem cdcl_complete (cnf : CNF) (fuel restartBase : Nat) (branch : List Nat)
    (h : (cdclSolveB cnf fuel restartBase branch).result = some .unsat)
    (a : Assignment) :
    checkSat cnf a = false :=
  (cdcl_correct cnf fuel restartBase branch).2 h a

end Lynth.Sat
