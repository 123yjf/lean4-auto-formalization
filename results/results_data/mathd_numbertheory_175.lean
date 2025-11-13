import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_175 :
  (2^2010 : ℕ) % 10 = 4 := by

  
  
  

  
  have h_cycle_1 : (2^1 : ℕ) % 10 = 2 := by
    
    norm_num

  have h_cycle_2 : (2^2 : ℕ) % 10 = 4 := by
    
    norm_num

  have h_cycle_3 : (2^3 : ℕ) % 10 = 8 := by
    
    norm_num

  have h_cycle_4 : (2^4 : ℕ) % 10 = 6 := by
    
    norm_num

  
  have h_cycle_5 : (2^5 : ℕ) % 10 = 2 := by
    
    norm_num

  
  

  
  have h_2010_mod_4 : 2010 % 4 = 2 := by
    
    norm_num

  
  
  have h_main : (2^2010 : ℕ) % 10 = 4 := by
    
    norm_num

  
  exact h_main
