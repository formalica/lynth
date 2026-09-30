import Mathlib
#eval (9 : Fin 9).val
#eval (8 : Fin 9).val
#eval (10 : Fin 9).val
example : (9 : Fin 9) = 0 := rfl
#print Fin.ofNat
