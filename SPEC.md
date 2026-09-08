# SYNTAX

- CAS+SMT solver which operates directly with Lean terms. users will interact with it by declaring type which he want to synthesize(like {f // cond f} subtype which mean find function f which will satisfy given condition or type can be some theorem) and `lynth` tactic will construct necessary Types and proofs of Props

# VERIFICATION

- at first step we will no prove correctness of tactic itself, but all meta code should not depends from built-in tactic of lean/mathlib so we can later able to prove them more easily
- all decision procedures should produce proof of proposition

# PATTERN MATCHING

- we can use `gpus` if it is needed
- we can use `discrimination trees` of lean to pattern match.
- each procedure can have many `properties` and we may need to lookup not only via terms but also via each property and each of them will have its own optimal data structure
- one of heuristic ways of finding/choosing fastest algorithms is just log their time spent on them on every run and `statistically` assign some weight to them. so there can be two overlapping procedures but after some testing we will start to choose only one of them for given problem. so there can be hard constraint of procedure which problem should satisfy and soft constraint which will be used to check whether it will be fast or not
- each decision procedures should produce can be can have information about very many `properties`(of holes which it fills) as much as possible because it will allow to more accurately pick decision procedures if there is two overlapping ones in same
- two decision procedures who solve same thing but they have different preconditions then it will be hard at runtime to find which precondition can be satisfiable, in this case during training we can detect such procedures and find fastest way by which we can check which of preconditions can be satisfied by any input problem

# LEARNING/TRAINING

- we can have theory explanations for each of procedures like in smt solvers
- later should be able to automatically find similarities between theorems,procedures and generalize/compress them, maybe introducing new DSLs for each subdomain. but currently we will rely on llms and assume that procedures written by them are highly generalized

# SIMPLIFICATION

- whatever we will define as simplest will be hard to prove because possible equivalent expressions are enormously big. instead of simplification we will use expressiveness(whether expression can be expressed by only given list of function) and user should choose which ones he want
- 

## Hypergeom functions

- we can start from integration/derivation/approximation of `hypergeometric functions`, user can ask to express it via given list of functions and to do it we should have separate equational rule for each simplified form of hypergeometric function and integral rule should detect whether function is hypergeometric or not then calculate integral and get new function and then should call rule of corresponding hypergeom equational rule and return it
- Implement various general decision procedures for hypergeoms and test them against tables of wolfram, remaining ones we can just cache
- we need map from both side of hypergeom table
- **MeijerGReduce** can be used to make hypergeom and just writing MeijerG[{{}, {}}, {{a}, {b}}, z^3] gives its simplified form
- in sympy, `hyperexpand` reduces/normalizes hypergeom by using certain properties of the pochhammer symbol and gamma function, then it tries to match the result with known hypergeom identities from internal table and returns the result. tables are listed [here](https://docs.sympy.org/latest/modules/simplify/hyperexpand.html). but wolfram have more identities in his table like [Specialized values](https://functions.wolfram.com/HypergeometricFunctions/Hypergeometric1F1/03/01/) section of each hypergeom function. but [For fixed z](https://functions.wolfram.com/HypergeometricFunctions/Hypergeometric1F1/03/02/) contains just reduced forms identities from Specialized values section for given contant values(we still can use them for just testing to make sure that our procedures are able to reduce all of them)
- to debug sympy we can run `export SYMPY_DEBUG=True isympy` and then `z = Symbol('z'); print(hyperexpand(hyper([3], [x], z)))`
- to convert into hypergeom we can use `from sympy.integrals.meijerint import _rewrite1; print(_rewrite1(sin(x),x))` or `_rewrite2` function