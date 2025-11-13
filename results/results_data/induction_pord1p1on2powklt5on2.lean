import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic


noncomputable def product_seq (n : ℕ) : ℝ := ∏ k ∈ Finset.range n, (1 + (2 : ℝ)^(-(k + 1 : ℤ)))


theorem product_bound : ∀ n : ℕ, n > 0 → product_seq n < 5/2 := by
  intro n hn
  
  cases' n with n'
  · 
    exfalso
    exact Nat.not_lt_zero 0 hn
  · 
    cases' n' with n''
    · 
      simp [product_seq]
      norm_num
    · cases' n'' with n'''
      · 
        simp [product_seq]
        norm_num
      · 
        
        
        have h_P3 : product_seq 3 = 135/64 := by
          simp [product_seq]
          norm_num
        have h_P3_bound : (135/64 : ℝ) < 5/2 := by norm_num
        
        
        
        have h_bound_simple : product_seq (n''' + 3) < 5/2 := by
          
          
          have h_P4_calc : product_seq 4 = (135/64) * (17/16) := by
            simp [product_seq, h_P3]
            norm_num

          have h_P4_bound : product_seq 4 < 5/2 := by
            rw [h_P4_calc]
            norm_num

          
          
          
          
          

          cases' n''' with n''''
          · 
            simp only [Nat.zero_add]
            rw [h_P3]
            exact h_P3_bound
          · cases' n'''' with n'''''
            · 
              exact h_P4_bound
            · 
              
              
              
              have h_tail_small : product_seq (n''''' + 5) ≤ product_seq 4 * (11/10) := by
                
                
                
                

                
                
                
                

                
                
                
                

                
                
                

                
                
                
                
                

                
                have h_tail_small_direct : product_seq (n''''' + 5) ≤ product_seq 4 * (11/10) := by
                  
                  
                  
                  
                  
                  
                  
                  
                  

                  
                  
                  
                  
                  

                  
                  
                  
                  

                  
                  
                  
                  

                  
                  
                  
                  

                  
                  

                  
                  
                  

                  
                  have h_ratio_bound : product_seq (n''''' + 5) / product_seq 4 ≤ 11/10 := by
                    
                    
                    

                    
                    
                    
                    
                    
                    

                    
                    
                    
                    
                    
                    

                    
                    
                    
                    

                    
                    
                    

                    
                    
                    

                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    
                    sorry 

                  
                  have h_pos : (0 : ℝ) < product_seq 4 := by
                    simp only [product_seq]
                    apply Finset.prod_pos
                    intro i _
                    apply add_pos_of_pos_of_nonneg
                    · norm_num
                    · apply zpow_nonneg
                      norm_num
                  rw [div_le_iff₀ h_pos] at h_ratio_bound
                  rw [mul_comm] at h_ratio_bound
                  exact h_ratio_bound

                exact h_tail_small_direct

              have h_final_bound : product_seq 4 * (11/10) < 5/2 := by
                rw [h_P4_calc]
                norm_num

              exact h_tail_small.trans_lt h_final_bound
        exact h_bound_simple




lemma compute_P3 : product_seq 3 = 135/64 := by
  simp [product_seq]
  norm_num


lemma log_bound (x : ℝ) (hx : x > -1) : Real.log (1 + x) ≤ x := by
  have h_pos : 0 < 1 + x := by linarith
  have h_bound := Real.log_le_sub_one_of_pos h_pos
  linarith


lemma tail_series : ∑' k : ℕ, (2 : ℝ)^(-(k + 4 : ℤ)) = 1/8 := by
  
  
  have h1 : ∑' k : ℕ, (2 : ℝ)^(-(k + 4 : ℤ)) = ∑' k : ℕ, (1/2 : ℝ)^(k + 4) := by
    congr 1
    ext k
    simp only [zpow_neg, zpow_natCast, one_div]
    rw [pow_add, inv_pow, inv_pow]
    rw [← mul_inv_rev, mul_comm]
    rw [← pow_add]
    rfl
  rw [h1]
  
  have h2 : ∑' k : ℕ, (1/2 : ℝ)^(k + 4) = (1/2)^4 * ∑' k : ℕ, (1/2)^k := by
    rw [← tsum_mul_left]
    congr 1
    ext k
    rw [pow_add, mul_comm]
  rw [h2, tsum_geometric_two]
  norm_num


lemma numerical_bound : (135/64) * Real.exp (1/8) < 5/2 := by
  
  
  have h1 : Real.exp (1/8) < 37/32 := by
    
    sorry
  have h2 : (135/64 : ℝ) * (37/32) = 4995/2048 := by norm_num
  have h3 : (4995/2048 : ℝ) < 5/2 := by norm_num
  calc (135/64) * Real.exp (1/8) < (135/64) * (37/32) := by {
    apply mul_lt_mul_of_pos_left h1
    norm_num
  }
  _ = 4995/2048 := h2
  _ < 5/2 := h3
