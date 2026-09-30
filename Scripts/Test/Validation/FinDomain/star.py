import z3
def region(r,c):
    if r==0: return 0 if c<6 else 1
    if r==1: return 0 if c<4 else (2 if c<7 else 1)
    if r==2: return 3 if c<2 else (0 if c<3 else (2 if c<6 else 1))
    if r==3: return 3 if c<2 else (2 if c<7 else (4 if c<9 else 5))
    if r==4: return 3 if c<2 else (2 if c<3 else (3 if c<4 else (4 if c<9 else 5)))
    if r==5: return 6 if c<1 else (3 if c<4 else (7 if c<5 else (4 if c<7 else 5)))
    if r==6: return 6 if c<1 else (8 if c<2 else (3 if c<4 else (7 if c<6 else (4 if c<7 else (9 if c<9 else 5)))))
    if r==7: return 6 if c<1 else (8 if c<2 else (7 if c<6 else (9 if c<9 else 5)))
    if r==8: return 6 if c<1 else (8 if c<5 else (7 if c<6 else (9 if c<9 else 5)))
    if r==9: return 6 if c<5 else (9 if c<8 else 5)
s=z3.Solver()
X=[[z3.Bool(f"x_{r}_{c}") for c in range(10)] for r in range(10)]
s.add(z3.PbEq([(X[r][c],1) for c in range(10)],2) for r in range(10))
s.add(z3.PbEq([(X[r][c],1) for r in range(10)],2) for c in range(10))
for k in range(10):
    s.add(z3.PbEq([(X[r][c],1) for r in range(10) for c in range(10) if region(r,c)==k],2))
for r in range(10):
    for c in range(10):
        for dr in (-1,0,1):
            for dc in (-1,0,1):
                rr,cc=r+dr,c+dc
                if 0<=rr<10 and 0<=cc<10 and not (dr==0 and dc==0):
                    s.add(z3.Or(z3.Not(X[r][c]), z3.Not(X[rr][cc])))
print("StarBattle10x10:", "SAT" if s.check()==z3.sat else "*** UNSAT ***")
if s.check()==z3.sat:
    m=s.model()
    g=[[1 if z3.is_true(m.evaluate(X[r][c])) else 0 for c in range(10)] for r in range(10)]
    for row in g: print("   ","".join("*" if v else "." for v in row))
    # uniqueness: block the model, re-check
    s.add(z3.Or([X[r][c] if g[r][c] else z3.Not(X[r][c]) for r in range(10) for c in range(10)]))
    print("   second solution?", "yes" if s.check()==z3.sat else "no -> UNIQUE")
