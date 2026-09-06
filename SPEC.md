# SYNTAX

- users will write subtype or proposition and call `lynth` tactic to fill solution and/or prove desired constraints

# VERFIFICAION

- at first step we will no prove correctness of tactic itself, but all meta code should not depends from built-in tactic of lean so we can later able to prove them more easily
- all decision procedures should produce proof of proposition

# HYPERGEOM

- we can start from integrals of `hypergeometric functions`, user can ask to express it via given list of functions and to do it we should have separate equational rule for each simplified form of hypergeometric function and integral rule should detect whether function is hypergeometric or not then calculate integral and get new function and then should call rule of corresponding hypergeom equational rule and return it
- Implement various general decision procedures for hypergeoms and test them against tables of wolfram, remaining ones we can just cache
- we need map from both side of hypergeom table
- **MeijerGReduce** can be used to make hypergeom and just writing MeijerG[{{}, {}}, {{a}, {b}}, z^3] gives its simplified form

# RUNTIME OPTIMIZATION

- one of heuristic ways of finding/choosing fastest algorithms is just log their time spent on them on every run and statistically assign some weight to them. so there can be two overlapping procedures but after some testing we will start to choose only one of them for given problem. so there can be hard constraint of procedure which problem should satisfy and soft constraint which will be used to check whether it will be fast or not
- each decision procedures should produce can be can have information about very many properties(of holes which it fills) as much as possible because it will allow to more accurately pick decision procedures if there is two overlapping ones in same
- two decision procedures who solve same thing but they have different preconditions then it will be hard at runtime to find which precondition can be satisfiable, in this case during training we can detect such procedures and fastest way by which we can check which of preconditions can be satisfied

# LEARNING/TRAINING

- we can have theory explanations for each of procedures like in smt solvers
- 

# SIMPLIFICATION

- whatever we will define as simplest will be hard to prove because possible equivalent expressions are enormously big. instead of simplification we will use expressiveness(whether expression can be expressed by only given list of function) and user should choose which ones he want
