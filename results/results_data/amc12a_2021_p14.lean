import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open BigOperators Finset Real




theorem amc12a_2021_p14 :
  (∑ k ∈ range 20, Real.logb (5^(k+1)) (3^((k+1)^2))) *
  (∑ k ∈ range 100, Real.logb (9^(k+1)) (25^(k+1))) = 21000 := by
  
  
  
  have h1 : ∑ k ∈ range 20, Real.logb (5^(k+1)) (3^((k+1)^2)) = 210 * Real.logb 5 3 := by
    
    have h_simp : ∀ k ∈ range 20, Real.logb (5^(k+1)) (3^((k+1)^2)) = (k+1) * Real.logb 5 3 := by
      intro k hk
      
      have h5_pos : (0 : ℝ) < 5 := by norm_num
      have h5_ne_one : (5 : ℝ) ≠ 1 := by norm_num
      have h3_pos : (0 : ℝ) < 3 := by norm_num
      have hk_pos : (0 : ℝ) < k + 1 := Nat.cast_add_one_pos k
      
      
      simp only [Real.logb, Real.log_pow]
      field_simp
      ring
    rw [sum_congr rfl h_simp, ← sum_mul]
    
    simp only [sum_range_succ]
    norm_num
  have h2 : ∑ k ∈ range 100, Real.logb (9^(k+1)) (25^(k+1)) = 100 * Real.logb 3 5 := by
    
    have h_simp : ∀ k ∈ range 100, Real.logb (9^(k+1)) (25^(k+1)) = Real.logb 3 5 := by
      intro k hk
      
      simp only [Real.logb]
      
      rw [Real.log_pow, Real.log_pow]
      
      have h25 : (25 : ℝ) = 5^2 := by norm_num
      have h9 : (9 : ℝ) = 3^2 := by norm_num
      rw [h25, h9, Real.log_pow, Real.log_pow]
      field_simp
      ring
    rw [sum_congr rfl h_simp, sum_const, card_range]
    norm_num
  have h3 : Real.logb 5 3 * Real.logb 3 5 = 1 := by
    
    
    simp only [Real.logb]
    
    
    field_simp
  rw [h1, h2]
  
  
  ring_nf
  rw [h3]
  norm_num
