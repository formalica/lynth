def solve(clues,label,note=""):
    g=[0]*81
    for (r,c),v in clues.items():
        i=9*r+c
        if g[i] and g[i]!=v: return print(f"{label}: CONFLICT at {(r,c)}")
        g[i]=v
    def ok(i,v):
        r,c=divmod(i,9)
        for j in range(9):
            if g[9*r+j]==v or g[9*j+c]==v: return False
        br,bc=(r//3)*3,(c//3)*3
        return all(g[9*(br+dr)+bc+dc]!=v for dr in range(3) for dc in range(3))
    def bt(i=0):
        while i<81 and g[i]: i+=1
        if i==81: return True
        for v in range(1,10):
            if ok(i,v):
                g[i]=v
                if bt(i+1): return True
                g[i]=0
        return False
    r=bt()
    if not r: print(f"{label}: *** UNSATISFIABLE *** ({len(clues)} clues) {note}")
    else:
        print(f"{label}: SATISFIABLE ({len(clues)} clues) {note}")
        for k in range(9): print("     "," ".join(str(x) for x in g[9*k:9*k+9]))
    return r

c9raw={(0,0):5,(0,1):3,(0,4):7,(1,0):6,(1,3):1,(1,4):9,(1,5):5,(2,1):9,(2,2):8,(2,7):6,
    (3,0):8,(3,4):6,(3,8):3,(4,0):4,(4,3):8,(4,5):3,(4,8):1,(5,0):7,(5,4):2,(5,8):6,
    (6,1):6,(6,6):2,(6,7):8,(7,3):4,(7,4):1,(7,5):9,(7,8):5,(8,4):8,(8,7):7,(8,8):9}
solve({k:v%9+1 for k,v in c9raw.items()},"Sudoku9        ","[Fin 9 numerals, 9->0 via mod]")
solve({k:v+1 for k,v in c9raw.items()},"Sudoku9 (naive)","[as if 1-indexed - what a reader assumes]")

ink={(0,2):5,(0,3):3,(1,0):8,(1,7):2,(2,1):7,(2,4):1,(2,6):5,(3,0):4,(3,5):5,(3,6):3,
     (4,1):1,(4,4):7,(4,8):6,(5,2):3,(5,3):2,(5,7):8,(6,1):6,(6,3):5,(6,8):9,(7,2):4,
     (7,7):3,(8,5):9,(8,6):7}
solve({k:v%9+1 for k,v in ink.items()},"Sudoku9Inkala  ","[Fin 9 numerals, 9->0 via mod]")

part={}
rows={1:{1:1,2:2,5:7,7:5,8:6},2:{1:5,3:7,4:9,5:3,6:2,8:8},3:{6:1},4:{2:1,4:2,5:4,8:5},
      5:{1:3,3:8,7:4,9:2},6:{2:7,5:8,6:5,8:1},7:{4:7},8:{2:8,4:4,5:2,6:3,7:7,9:1},
      9:{2:3,3:4,5:1,8:2,9:8}}
for r,d in rows.items():
    for c,v in d.items(): part[(r-1,c-1)]=v
solve(part,"Sudoku9Partial ","[custom Val v1..v9 = digits 1..9]")
