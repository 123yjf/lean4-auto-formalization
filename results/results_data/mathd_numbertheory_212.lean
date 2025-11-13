import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_212 :
  (16^17 * 17^18 * 18^19 : ℕ) % 10 = 8 := by

  

  
  have h_16_17 : (16^17 : ℕ) % 10 = 6 := by
    
    have h_16_mod : (16 : ℕ) % 10 = 6 := by
      
      norm_num
    have h_6_pow : ∀ k : ℕ, k ≥ 1 → (6^k : ℕ) % 10 = 6 := by
      
      intro k hk
      induction' k using Nat.strong_induction_on with k ih
      cases' k with k
      · contradiction
      cases' k with k
      · norm_num
      · have h_rec : (6^(k + 2) : ℕ) % 10 = 6 := by
          rw [pow_succ, Nat.mul_mod]
          have h_prev : (6^(k + 1) : ℕ) % 10 = 6 := ih (k + 1) (by simp) (by simp)
          rw [h_prev]
        exact h_rec
    
    rw [← h_16_mod, Nat.pow_mod, h_6_pow 17 (by norm_num)]

  
  have h_17_18 : (17^18 : ℕ) % 10 = 9 := by
    
    have h_17_mod : (17 : ℕ) % 10 = 7 := by
      
      norm_num
    have h_7_cycle : (7^1 : ℕ) % 10 = 7 ∧ (7^2 : ℕ) % 10 = 9 ∧
                     (7^3 : ℕ) % 10 = 3 ∧ (7^4 : ℕ) % 10 = 1 := by
      
      norm_num
    have h_18_mod_4 : 18 % 4 = 2 := by
      
      norm_num
    
    
    norm_num [h_17_mod, h_7_cycle, h_18_mod_4]

  
  have h_18_19 : (18^19 : ℕ) % 10 = 2 := by
    
    have h_18_mod : (18 : ℕ) % 10 = 8 := by
      
      norm_num
    have h_8_cycle : (8^1 : ℕ) % 10 = 8 ∧ (8^2 : ℕ) % 10 = 4 ∧
                     (8^3 : ℕ) % 10 = 2 ∧ (8^4 : ℕ) % 10 = 6 := by
      
      norm_num
    have h_19_mod_4 : 19 % 4 = 3 := by
      
      norm_num
    
    
    norm_num [h_18_mod, h_8_cycle, h_19_mod_4]

  
  have h_product : (6 * 9 * 2 : ℕ) % 10 = 8 := by
    
    norm_num

  
  have h_final : (16^17 * 17^18 * 18^19 : ℕ) % 10 = 8 := by
    
    norm_num [h_16_17, h_17_18, h_18_19]
  exact h_final
