implement procedures for interval arithmetic so that most of tests will pass, they are written for real but framework should work for complex type too. you can add few tests for complex if you want

we should have framework which will allow to easily add support of new real/complex functions
all tests should be proven by just calling lynth tactic

here is projects which you can use
~/flint contain fast convergance approximation algorithms for vaious functions, already compiled
~/leancert is lean library which can prove theorems about interval arithmetic, but it is not allowing to do verified computation and get values, you are free and I recomend to copy whole leancert and start to heavily edit it and adopt to lynth without spending lot of time to making everything from scratch
~/interval-4.11.5 interval arithetic tactic which able to prove and also have interval_intro tatci which allow to numerically compute expression with given precision, so this is what we want but we have more functional style of usage of lynth tactic, do not try to spent time to compile it 

since I have little knowledge in this area, I can not properly review your spec I can only answer to your high level questions, I recomend to write some very big separate implementation spec with lot of details and code snippets, so implementation spec will be preserved accross various sessions and various agents

some test may be unsolvable, but they are very little because most of tests are numerically checked by other tools

important ones are approximation of various composition of real functions, integrals,infinite sums, finite sums and also meta tests where we not only need to approximate for given values but for any arguemnt(or function which will give good aproximations for any value fr given range and outside of that range is not important)

you can investigate, then ask me high level questions/decisions to made, then write very detailed multifile spec and start to implement