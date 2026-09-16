# Procedure registry

| Procedure | Internal language | Oracle | Reconstruction | Status |
|---|---|---|---|---|
| `Sat` (`Lynth/Sat`) | `CNF` (`Syntax.lean`), `PropForm` skeleton (`Encode.lean`) | CDCL: reason-tracked propagation, first-UIP learning with recorded resolution traces (`checkTrace`, fuzz-validated), backjump, VSIDS, geometric restarts (`Cdcl.lean`); DPLL reference (`Solver.lean`); Tseitin validity oracle over goal+hyps | oracle-guided `assumption/rfl/simp_all/grind/decide`; `lynth_sat_resolve` activates with trace validation | CDCL done; watched literals TODO |
| `Arith` (`Lynth/Arith`) | `LinSys` (`Linear.lean`); `LeC` ℚ-systems (`Fourier.lean`) | FM elimination with Farkas lineage + validation (`checkCert`, fuzz-verified) + tableau Simplex à la Dutertre–de Moura + branch-and-bound for ℤ-completeness, differential-tested (`Fourier.solve`, `Simplex.solve`, `BranchBound.bb`); `Recognize` translates `Int`/`Nat` comparisons exactly (`+1` shifts for strict) | verified certs traced; kernel-checked `omega` closes | Farkas extraction from Simplex rows + `lynth_farkas` activation TODO |
| `EUF` (`Lynth/Euf`) | equality graph over `Eq` hyps (`Closure.lean` union-find) | BFS path search + congruence fixpoint (`congr` edges) + `Ne`/`False` close by contradiction | `Eq.trans`/`Eq.symm`/`congr` proof terms, kernel-checked, zero axioms | done; failure shares derived equalities into context (`shareDerived`) for later procedures |
| `Ring` (`Lynth/Ring`) | semiring identities | kernel-checked `ring` normalizer (cf. Z3 `grobner`/`polynomial`) | `ring` | done |
| `Witness` (`Lynth/Witness`) | `Subtype` + `Exists` goals | `Nat` range + `Int` interleave enumeration (bound 64) + `Bool` | explicit `Subtype.mk`/`Exists.intro` terms + `decide/omega/simp_all/rfl` side close | `Nat`+`Int`+`Bool` done; other domains TODO |
| Simplex core | — | — | — | DONE (`Simplex.lean`); Farkas extraction TODO |
| CDCL(T) loop | — | — | — | TODO |

Reconstruction theorems live in `Lynth/Axioms.lean` as sound,
checker-conditioned statements (`lynth_sat_resolve`, `lynth_farkas`;
no `axiom`s, no `sorry`s anywhere). Witness reconstruction is direct
(`Subtype.mk`). `sorry` is banned.
