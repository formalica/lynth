import Lean

/-!
# `lynth_exact` simp set

Lemmas tagged `@[lynth_exact]` let the reifier evaluate closed terms to exact
rationals (`norm_num` + default simp set + this set).  The head constants of
their left-hand sides are the *triggers*: the simp fallback only runs on closed
terms mentioning a trigger.  See `docs/interval/03-expr-registry.md §7`.
-/

register_simp_attr lynth_exact
