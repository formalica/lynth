L=[[0,0,0,0,0,0,1,1,1,1],[0,0,0,0,2,2,2,1,1,1],[3,3,0,2,2,2,1,1,1,1],
[3,3,2,2,2,2,2,4,4,5],[3,3,2,3,4,4,4,4,4,5],[6,3,3,3,7,4,4,5,5,5],
[6,8,3,3,7,7,4,9,9,5],[6,8,7,7,7,7,9,9,9,5],[6,8,8,8,8,7,9,9,9,5],
[6,6,6,6,6,9,9,9,5,5]]
G=["..*...*...","....*...*.","*.*.......",".....*...*","...*...*..",
   "*........*","....*.*...",".*......*.","...*.*....",".*.....*.."]
S=[[1 if ch=='*' else 0 for ch in row] for row in G]
ok=True
def chk(name,cond):
    global ok
    print(f"  {name}: {'OK' if cond else 'FAIL'}")
    if not cond: ok=False
chk("2 stars per row", all(sum(r)==2 for r in S))
chk("2 stars per col", all(sum(S[r][c] for r in range(10))==2 for c in range(10)))
for k in range(10):
    n=sum(S[r][c] for r in range(10) for c in range(10) if L[r][c]==k)
    if n!=2: chk(f"region {k} has {n} stars",False)
chk("2 stars per region (all 10)", all(sum(S[r][c] for r in range(10) for c in range(10) if L[r][c]==k)==2 for k in range(10)))
adj=True
for r in range(10):
    for c in range(10):
        if S[r][c]:
            for dr in(-1,0,1):
                for dc in(-1,0,1):
                    rr,cc=r+dr,c+dc
                    if 0<=rr<10 and 0<=cc<10 and (dr or dc) and S[rr][cc]: adj=False
chk("no two stars adjacent (incl. diagonal)", adj)
print("\nVERDICT:", "grid is a VALID StarBattle solution -> goal is SATISFIABLE" if ok else "INVALID")
