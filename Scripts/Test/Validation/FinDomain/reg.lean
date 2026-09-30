import Lynth
-- regionID transcribed verbatim from Test/FinDomain/StarBattle10x10.lean
def regionID : Fin 10 → Fin 10 → Fin 10
  | 0, c => if c.val < 6 then 0 else 1
  | 1, c => if c.val < 4 then 0 else if c.val < 7 then 2 else 1
  | 2, c => if c.val < 2 then 3 else if c.val < 3 then 0 else if c.val < 6 then 2 else 1
  | 3, c => if c.val < 2 then 3 else if c.val < 7 then 2 else if c.val < 9 then 4 else 5
  | 4, c => if c.val < 2 then 3 else if c.val < 3 then 2 else if c.val < 4 then 3 else if c.val < 9 then 4 else 5
  | 5, c => if c.val < 1 then 6 else if c.val < 4 then 3 else if c.val < 5 then 7 else if c.val < 7 then 4 else 5
  | 6, c => if c.val < 1 then 6 else if c.val < 2 then 8 else if c.val < 4 then 3 else if c.val < 6 then 7 else if c.val < 7 then 4 else if c.val < 9 then 9 else 5
  | 7, c => if c.val < 1 then 6 else if c.val < 2 then 8 else if c.val < 6 then 7 else if c.val < 9 then 9 else 5
  | 8, c => if c.val < 1 then 6 else if c.val < 5 then 8 else if c.val < 6 then 7 else if c.val < 9 then 9 else 5
  | 9, c => if c.val < 5 then 6 else if c.val < 8 then 9 else 5
def mk (n : Nat) : Fin 10 := ⟨n % 10, by omega⟩
def mk (n : Nat) : Fin 10 := ⟨n % 10, by omega⟩
#eval (List.range 10).map (fun r =>
  (List.range 10).map (fun c => (regionID (mk r) (mk c)).toNat))
