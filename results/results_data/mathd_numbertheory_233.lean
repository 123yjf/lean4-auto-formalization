import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD


theorem mathd_numbertheory_233 :
  ∃ b : ℕ, b < 121 ∧ (24 * b) % 121 = 1 ∧ b = 116 := by

  
  use 116
  constructor
  · 
    norm_num
  constructor
  · 
    
    have h_euclidean_1 : 121 = 5 * 24 + 1 := by
      
      norm_num

    have h_euclidean_2 : 24 = 24 * 1 + 0 := by
      
      norm_num

    have h_gcd : Nat.gcd 24 121 = 1 := by
      
      norm_num

    
    have h_linear_comb : 1 = 121 - 5 * 24 := by
      
      norm_num

    
    have h_neg_five_equiv : (-5 : ℤ) + 121 = 116 := by
      
      norm_num

    
    have h_verification : 24 * 116 = 2784 := by
      
      norm_num

    have h_division : 2784 = 23 * 121 + 1 := by
      
      norm_num

    
    have h_nat_mod : (24 * 116) % 121 = 1 := by
      
      norm_num

    exact h_nat_mod

  · 
    rfl
