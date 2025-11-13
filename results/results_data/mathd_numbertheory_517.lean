import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_517 :
  (121 * 122 * 123) % 4 = 2 := by

  
  
  have h_121_mod : (121 : ℕ) % 4 = 1 := by
    
    norm_num

  have h_122_mod : (122 : ℕ) % 4 = 2 := by
    
    norm_num

  have h_123_mod : (123 : ℕ) % 4 = 3 := by
    
    norm_num

  
  have h_product_residues : (1 * 2 * 3) % 4 = 2 := by
    
    norm_num

  
  have h_mod_calc : (121 * 122 * 123) % 4 = ((121 % 4) * (122 % 4) * (123 % 4)) % 4 := by
    
    simp only [← Nat.mul_mod]

  
  calc (121 * 122 * 123) % 4
    = ((121 % 4) * (122 % 4) * (123 % 4)) % 4 := h_mod_calc
    _ = (1 * 2 * 3) % 4 := by simp only [h_121_mod, h_122_mod, h_123_mod]
    _ = 2 := h_product_residues
