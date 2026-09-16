# Procedure registry

| Procedure | Internal language | Oracle | Reconstruction | Status |
|---|---|---|---|---|
| `Sat` (`Lynth/Sat`) | `CNF` (`Syntax.lean`), `PropForm` skeleton (`Encode.lean`) | DPLL+unit+pure (`Solver.lean`); Tseitin validity oracle over goal skeleton (`Abstract.lean`, hypotheses TODO) | oracle-guided `assumption/rfl/simp_all/grind/decide`; cert via `lynth_sat_resolve` (axiom) | basic |
| `Arith` (`Lynth/Arith`) | `LinSys` (`Linear.lean`); `LeC` ℚ-systems (`Fourier.lean`) | FM elimination with Farkas lineage (`Fourier.solve`); `Recognize` translates `Int`/`Nat` comparisons exactly (`+1` shifts for strict) | FM cert traced; kernel-checked `omega` closes | FM core done; Simplex core + `lynth_farkas` reconstruction TODO |
| `EUF` (`Lynth/Euf`) | equality graph over `Eq` hyps (`Closure.lean` union-find) | BFS path search + congruence fixpoint (`congr` edges) | `Eq.trans`/`Eq.symm`/`congr` proof terms, kernel-checked, zero axioms | done; failure shares derived equalities into context (`shareDerived`) for later procedures |
| `Witness` (`Lynth/Witness`) | `Subtype` goals | `Nat` range + `Int` interleave enumeration (bound 64) | explicit `Subtype.mk` term + `decide/omega/simp_all/rfl` side close | `Nat`+`Int` done; other domains TODO |
| EUF / congruence closure | — | — | — | TODO |
| Simplex core | — | — | — | TODO |
| CDCL(T) loop | — | — | — | TODO |

Reconstruction theorems that are correct but unproved live as axioms in
`Lynth/Axioms.lean` (`lynth_sat_resolve`, `lynth_farkas`, `lynth_witness`).
` sorry` is banned; use an axiom + a registry row instead.
