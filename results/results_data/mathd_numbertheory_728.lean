import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring




theorem mathd_numbertheory_728 : (29 : ZMod 7) ^ 13 - (5 : ZMod 7) ^ 13 = 3 := by
  
  have h_prime : Nat.Prime 7 := by
    
    decide
  haveI : Fact (Nat.Prime 7) := ⟨h_prime⟩

  
  
  have h_29_mod : (29 : ZMod 7) = 1 := by
    rfl

  
  
  have h_fermat : (5 : ZMod 7) ^ 6 = 1 := by
    
    rfl

  
  
  have h_13_mod : 13 = 2 * 6 + 1 := by norm_num

  
  have h_29_pow : (29 : ZMod 7) ^ 13 = 1 := by
    rw [h_29_mod, one_pow]

  
  have h_5_pow : (5 : ZMod 7) ^ 13 = 5 := by
    
    rfl

  
  rw [h_29_pow, h_5_pow]
  
  rfl
