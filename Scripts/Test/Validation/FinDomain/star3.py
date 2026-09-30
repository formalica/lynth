import z3
L=[[0,0,0,0,0,0,1,1,1,1],[0,0,0,0,2,2,2,1,1,1],[3,3,0,2,2,2,1,1,1,1],
[3,3,2,2,2,2,2,4,4,5],[3,3,2,3,4,4,4,4,4,5],[6,3,3,3,7,4,4,5,5,5],
[6,8,3,3,7,7,4,9,9,5],[6,8,7,7,7,7,9,9,9,5],[6,8,8,8,8,7,9,9,9,5],
[6,6,6,6,6,9,9,9,5,5]]
G=["..*...*...","....*...*.","*.*.......",".....*...*","...*...*..",
   "*........*","....*.*...",".*......*.","...*.*....",".*.....*.."]
g0=[[1 if ch=="*" else 0 for ch in row] for row in G]
s=z3.Solver(); X=[[z3.Bool(f"v{r}_{c}") for c in range(10)] for r in range(10)]
for r in range(10): s.add(z3.PbEq([(X[r][c],1) for c in range(10)],2))
for c in range(10): s.add(z3.PbEq([(X[r][c],1) for r in range(10)],2))
for k in range(10): s.add(z3.PbEq([(X[r][c],1) for r in range(10) for c in range(10) if L[r][c]==k],2))
for r in range(10):
    for c in range(10):
        for dr in(-1,0,1):
            for dc in(-1,0,1):
                rr,cc=r+dr,c+dc
                if 0<=rr<10 and 0<=cc<10 and (dr or dc):
                    s.add(z3.Or(z3.Not(X[r][c]),z3.Not(X[rr][cc])))
print("g0 is a model?    ", s.check()==z3.sat)
# g0 has (0,0) empty. Forcing it to be a star gives a DIFFERENT solution if SAT.
s.push(); s.add(X[0][0])
r2=s.check()
print("force (0,0)=star -> ", "SAT, so a solution exists with (0,0) starred: NOT UNIQUE" if r2==z3.sat else "UNSAT: g0 is the unique solution")
s.pop()
s.push(); s.add(z3.Not(X[0][0]), z3.Not(X[0][2]))
r3=s.check()
print("force (0,0),(0,2) empty -> ", "SAT: another solution exists, NOT UNIQUE" if r3==z3.sat else "UNSAT")
s.pop()
