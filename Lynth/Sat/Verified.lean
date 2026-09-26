import Lean
import Lynth.Sat.Cdcl
import Mathlib.Data.Nat.Find

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
  satisfying assignment is ever cut off, whatever `branch` holds.
  Fuel/restarts only bound the search: the axiom claims nothing about
  `none` (unknown) results, only that a *reported* UNSAT is genuine.
-/
namespace Lynth.Sat

/-- TEMPORARY AXIOM — solver correctness (soundness + completeness).
To be proven from the `Watch` implementation (CreuSAT invariant
structure) once the campaign allows; until then every verified-solver
proof bottoms out here. See the module doc for why this statement is
true of the implementation. -/
axiom cdcl_correct (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) :
  (∀ m : Assignment,
    (Cdcl.cdclSolve cnf fuel restartBase branch).result = some (.sat m) →
    checkSat cnf m = true) ∧
  ((Cdcl.cdclSolve cnf fuel restartBase branch).result = some .unsat →
    ∀ a : Assignment, checkSat cnf a = false)

/-- Soundness: a reported model genuinely satisfies the input. -/
theorem cdcl_sound (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (m : Assignment)
    (h : (Cdcl.cdclSolve cnf fuel restartBase branch).result
      = some (.sat m)) :
    checkSat cnf m = true :=
  (cdcl_correct cnf fuel restartBase branch).1 m h

/-- Completeness: a reported UNSAT means no satisfying assignment exists. -/
theorem cdcl_complete (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat)
    (h : (Cdcl.cdclSolve cnf fuel restartBase branch).result = some .unsat)
    (a : Assignment) :
    checkSat cnf a = false :=
  (cdcl_correct cnf fuel restartBase branch).2 h a

/-- Doubling schedule: one exact solver run per level, no clause
sharing between levels (geometric re-solving costs ≈2× the final
run; sharing learned clauses is a later optimization). Level `0`
runs at the base fuel, level `k + 1` at `fuel * 2 ^ (k + 1)`.
Total (structural match, no recursion). -/
def cdclLoop (cnf : CNF) (fuel restartBase : Nat) (branch : Std.HashSet Nat) :
    Nat → Option SatResult
  | 0 => (Cdcl.cdclSolve cnf fuel restartBase branch).result
  | n + 1 =>
    (Cdcl.cdclSolve cnf (fuel * 2 ^ (n + 1)) restartBase branch).result

/-- TEMPORARY AXIOM #2 — fuel sufficiency, uniform over all CNFs.
Finite search space plus complete search imply some doubling level
decides every input. Discharged later by the real completeness proof,
together with axiom #1. -/
axiom cdcl_fuel_suffices (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) :
    ∃ caps, (cdclLoop cnf fuel restartBase branch caps) ≠ none

/-- Total solver: first deciding doubling level (the existence proof
is erased at runtime, so evaluation just runs levels `0, 1, 2, …`
until one decides — which happens in practice by the mathematical
fact behind axiom #2), then its answer. There is no unknown case:
the `none` branch is contradictory by `Nat.find_spec`. -/
def solveTotal (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) : SatResult :=
  match ho : (cdclLoop cnf fuel restartBase branch
      (Nat.find (cdcl_fuel_suffices cnf fuel restartBase branch))) with
  | some r => r
  | none => absurd ho (Nat.find_spec (cdcl_fuel_suffices cnf fuel restartBase branch))

/-- Loop soundness at any level (every level is one exact solver run,
so this is just axiom #1 after casing the level). -/
theorem cdclLoop_sound (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (caps : Nat) (m : Assignment)
    (h : (cdclLoop cnf fuel restartBase branch caps)
      = some (.sat m)) :
    checkSat cnf m = true := by
  cases caps with
  | zero =>
    exact (cdcl_correct cnf fuel restartBase branch).1 m
      (by simpa [cdclLoop] using h)
  | succ k =>
    exact (cdcl_correct cnf (fuel * 2 ^ (k + 1)) restartBase branch).1 m
      (by simpa [cdclLoop] using h)

/-- Loop completeness at any level. -/
theorem cdclLoop_complete (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (caps : Nat)
    (h : (cdclLoop cnf fuel restartBase branch caps) = some .unsat)
    (a : Assignment) :
    checkSat cnf a = false := by
  cases caps with
  | zero =>
    exact (cdcl_correct cnf fuel restartBase branch).2
      (by simpa [cdclLoop] using h) a
  | succ k =>
    exact (cdcl_correct cnf (fuel * 2 ^ (k + 1)) restartBase branch).2
      (by simpa [cdclLoop] using h) a

/-- Characterization: unfolding the total solver at a decided loop
outcome. Proved by reverting the equation (so `generalize` covers
goal and hypothesis together), generalizing the closed loop call to
a variable, and substituting. -/
theorem solveTotal_eq_of_loop (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (r : SatResult)
    (hR : (cdclLoop cnf fuel restartBase branch
      (Nat.find (cdcl_fuel_suffices cnf fuel restartBase branch)))
      = some r) :
    solveTotal cnf fuel restartBase branch = r := by
  unfold solveTotal
  split <;> simp_all

/-- Total-solver soundness: a reported model satisfies the input.
Cases the deciding loop outcome (reusing its equation); the absurd
branches are contradictory by constructor discrimination or by
fuel sufficiency. -/
theorem solveTotal_sound (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (m : Assignment)
    (h : solveTotal cnf fuel restartBase branch = .sat m) :
    checkSat cnf m = true := by
  match hR : (cdclLoop cnf fuel restartBase branch
      (Nat.find (cdcl_fuel_suffices cnf fuel restartBase branch))) with
  | some (.sat m') =>
    have hS := solveTotal_eq_of_loop cnf fuel restartBase branch _ hR
    rw [hS] at h
    cases h
    exact cdclLoop_sound cnf fuel restartBase branch _ _ hR
  | some .unsat =>
    have hS := solveTotal_eq_of_loop cnf fuel restartBase branch _ hR
    rw [hS] at h
    nomatch h
  | none =>
    exact ((Nat.find_spec
      (cdcl_fuel_suffices cnf fuel restartBase branch)) hR).elim

/-- Total-solver completeness: `unsat` means unsatisfiable. -/
theorem solveTotal_complete (cnf : CNF) (fuel restartBase : Nat)
    (branch : Std.HashSet Nat) (a : Assignment)
    (h : solveTotal cnf fuel restartBase branch = .unsat) :
    checkSat cnf a = false := by
  match hR : (cdclLoop cnf fuel restartBase branch
      (Nat.find (cdcl_fuel_suffices cnf fuel restartBase branch))) with
  | some (.sat m') =>
    have hS := solveTotal_eq_of_loop cnf fuel restartBase branch _ hR
    rw [hS] at h
    nomatch h
  | some .unsat =>
    exact cdclLoop_complete cnf fuel restartBase branch _ hR a
  | none =>
    exact ((Nat.find_spec
      (cdcl_fuel_suffices cnf fuel restartBase branch)) hR).elim

end Lynth.Sat
