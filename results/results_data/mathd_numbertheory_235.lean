import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_235 :
  (29 * 79 + 31 * 81) % 10 = 2 := by

  

  
  have h_29_mod : (29 : ℕ) % 10 = 9 := by
    
    norm_num

  have h_79_mod : (79 : ℕ) % 10 = 9 := by
    
    norm_num

  have h_31_mod : (31 : ℕ) % 10 = 1 := by
    
    norm_num

  have h_81_mod : (81 : ℕ) % 10 = 1 := by
    
    norm_num

  
  have h_mod_calc : (29 * 79 + 31 * 81) % 10 = (9 * 9 + 1 * 1) % 10 := by
    
    simp only [← Nat.mul_mod, ← Nat.add_mod, h_29_mod, h_79_mod, h_31_mod, h_81_mod]

  
  have h_compute : (9 * 9 + 1 * 1) % 10 = 2 := by
    
    norm_num

  
  have h_verification : 29 * 79 + 31 * 81 = 4802 := by
    
    norm_num

  have h_verify_mod : (4802 : ℕ) % 10 = 2 := by
    
    norm_num

  
  rw [h_mod_calc, h_compute]
