import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.NormNum.Prime


theorem mathd_numbertheory_328 : (5 : ZMod 7) ^ 999999 = 6 := by
  
  have h1 : (5 : ZMod 7) ^ 6 = 1 := by
    rfl

  
  have h2 : 999999 % 6 = 3 := by
    norm_num

  
  have h3 : (5 : ZMod 7) ^ 999999 = (5 : ZMod 7) ^ 3 := by
    rw [pow_eq_pow_mod 999999 h1, h2]

  
  have h4 : (5 : ZMod 7) ^ 3 = 6 := by
    rfl

  
  rw [h3, h4]
