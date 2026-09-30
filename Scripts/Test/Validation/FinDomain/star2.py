import z3
L=[[0,0,0,0,0,0,1,1,1,1],[0,0,0,0,2,2,2,1,1,1],[3,3,0,2,2,2,1,1,1,1],
[3,3,2,2,2,2,2,4,4,5],[3,3,2,3,4,4,4,4,4,5],[6,3,3,3,7,4,4,5,5,5],
[6,8,3,3,7,7,4,9,9,5],[6,8,7,7,7,7,9,9,9,5],[6,8,8,8,8,7,9,9,9,5],
[6,6,6,6,6,9,9,9,5,5]]
def mk():
    s=z3.Solver()
    X=[[z3.Bool(f"x_{r}_{c}") for c in range(10)] for r in range(10)]
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
    return s,X
s,X=mk(); sols=[]
while s.check()==z3.sat and len(sols)<5:
    m=s.model(); g=[[1 if z3.is_true(m.evaluate(X[r][c])) else 0 for c in range(10)] for r in range(10)]
    sols.append(g)
    s.add(z3.Or([X[r][c] if g[r][c] else z3.Not(X[r][c]) for r in range(10) for c in range(10)]))
print(f"StarBattle10x10: {len(sols)} solution(s) found (capped at 5)")
for i,g in enumerate(sols):
    print(f"  --- solution {i+1}")
    for row in g: print("     ","".join("*" if v else "." for v in row))
