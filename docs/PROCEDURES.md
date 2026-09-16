# Procedure registry

| Procedure | Internal language | Oracle | Reconstruction | Status |
|---|---|---|---|---|
| `Sat` (`Lynth/Sat`) | `CNF` (`Syntax.lean`), `PropForm` skeleton (`Encode.lean`) | CDCL: reason-tracked propagation, first-UIP learning with recorded resolution traces (`checkTrace`, fuzz-validated), backjump, VSIDS, geometric restarts (`Cdcl.lean`); DPLL reference (`Solver.lean`); Tseitin validity oracle over goal+hyps | oracle-guided `assumption/rfl/simp_all/grind/decide`; `lynth_sat_resolve` activates with trace validation | CDCL done; watched literals TODO |
| `Arith` (`Lynth/Arith`) | `LinSys` (`Linear.lean`); `LeC` ℚ-systems (`Fourier.lean`) | FM elimination with Farkas lineage + validation (`checkCert`, fuzz-verified) + tableau Simplex à la Dutertre–de Moura + branch-and-bound for ℤ-completeness, differential-tested (`Fourier.solve`, `Simplex.solve`, `BranchBound.bb`); `Recognize` translates `Int`/`Nat` comparisons exactly (`+1` shifts for strict) | verified certs traced; kernel-checked `omega` closes | PROVED: `FarkasSound.farkas_sound` + `checkCert_sound` (native axioms, zero sorries); remaining: Lean-term denotes link, Simplex-row extraction, `lynth_farkas` activation |
| `EUF` (`Lynth/Euf`) | equality graph over `Eq` hyps (`Closure.lean` union-find) | BFS path search + congruence fixpoint (`congr` edges) + `Ne`/`False` close by contradiction | `Eq.trans`/`Eq.symm`/`congr` proof terms, kernel-checked, zero axioms | done; failure shares derived equalities into context (`shareDerived`) for later procedures |
| `Ring` (`Lynth/Ring`) | semiring identities | kernel-checked `ring` normalizer (cf. Z3 `grobner`/`polynomial`) | `ring` | done |
| `Nlin` (`Lynth/Nlin`) | polynomial inequalities | kernel-checked `nlinarith` (Positivstellensatz-style products) | `nlinarith` | done |
| `Witness` (`Lynth/Witness`) | `Subtype` + `Exists` goals | `Nat`/`Int` enumeration (256) + `Bool` + diagonal `Prod` pairs + complete `Fin n` | explicit `Subtype.mk`/`Exists.intro` terms + `decide/rfl/omega/simp_all` side close | done for scalars, pairs, finite types; other domains TODO |
| Simplex core | — | — | — | DONE (`Simplex.lean`); Farkas extraction TODO |
| Combination model | sequential explanation-passing (no SMT loop, per SPEC) | EUF shares proven equalities; all procedures read the enriched context | — | done (this IS the combination mechanism) |

Reconstruction theorems live in `Lynth/Axioms.lean` as sound,
checker-conditioned statements (`lynth_sat_resolve`, `lynth_farkas`;
no `axiom`s, no `sorry`s anywhere). Witness reconstruction is direct
(`Subtype.mk`). `sorry` is banned.
