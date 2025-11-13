import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_345 :
  (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 = 0 := by

  
  
  have h_2000_mod : (2000 : ℕ) % 7 = 5 := by
    
    norm_num

  have h_2001_mod : (2001 : ℕ) % 7 = 6 := by
    
    norm_num

  have h_2002_mod : (2002 : ℕ) % 7 = 0 := by
    
    norm_num

  have h_2003_mod : (2003 : ℕ) % 7 = 1 := by
    
    norm_num

  have h_2004_mod : (2004 : ℕ) % 7 = 2 := by
    
    norm_num

  have h_2005_mod : (2005 : ℕ) % 7 = 3 := by
    
    norm_num

  have h_2006_mod : (2006 : ℕ) % 7 = 4 := by
    
    norm_num

  
  have h_sum_residues : (5 + 6 + 0 + 1 + 2 + 3 + 4) % 7 = 0 := by
    
    norm_num

  
  have h_mod_calc : (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7 =
    ((2000 % 7) + (2001 % 7) + (2002 % 7) + (2003 % 7) + (2004 % 7) + (2005 % 7) + (2006 % 7)) % 7 := by
    
    simp only [← Nat.add_mod]

  
  calc (2000 + 2001 + 2002 + 2003 + 2004 + 2005 + 2006) % 7
    = ((2000 % 7) + (2001 % 7) + (2002 % 7) + (2003 % 7) + (2004 % 7) + (2005 % 7) + (2006 % 7)) % 7 := h_mod_calc
    _ = (5 + 6 + 0 + 1 + 2 + 3 + 4) % 7 := by simp only [h_2000_mod, h_2001_mod, h_2002_mod, h_2003_mod, h_2004_mod, h_2005_mod, h_2006_mod]
    _ = 0 := h_sum_residues
