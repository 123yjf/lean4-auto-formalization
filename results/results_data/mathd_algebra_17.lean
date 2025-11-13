import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith



theorem mathd_algebra_17 :
  ∀ a : ℝ, (Real.sqrt (4 + Real.sqrt (16 + 16 * a)) + Real.sqrt (1 + Real.sqrt (1 + a)) = 6) ↔ (a = 8) := by
  intro a
  constructor
  · 
    intro h
    
    have domain_constraint : a ≥ -1 := by
      
      
      by_contra h_neg
      push_neg at h_neg
      
      have h_inner_zero : Real.sqrt (1 + a) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        linarith
      
      have h_outer : Real.sqrt (1 + Real.sqrt (1 + a)) = 1 := by
        rw [h_inner_zero]
        norm_num
      
      have h_sixteen : Real.sqrt (16 + 16 * a) = 0 := by
        apply Real.sqrt_eq_zero_of_nonpos
        linarith
      
      have h_four : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 := by
        rw [h_sixteen]
        simp only [add_zero]
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      
      rw [h_four, h_outer] at h
      norm_num at h
    
    have factorization : Real.sqrt (4 + Real.sqrt (16 + 16 * a)) = 2 * Real.sqrt (1 + Real.sqrt (1 + a)) := by
      
      have h1 : 16 + 16 * a = 16 * (1 + a) := by ring
      rw [h1]
      
      have h_nonneg : 0 ≤ 1 + a := by linarith [domain_constraint]
      have h2 : Real.sqrt (16 * (1 + a)) = 4 * Real.sqrt (1 + a) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16) (1 + a)]
        rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      rw [h2]
      
      have h3 : 4 + 4 * Real.sqrt (1 + a) = 4 * (1 + Real.sqrt (1 + a)) := by ring
      rw [h3]
      have h_inner_nonneg : 0 ≤ 1 + Real.sqrt (1 + a) := by
        apply add_nonneg
        · norm_num
        · exact Real.sqrt_nonneg _
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4) (1 + Real.sqrt (1 + a))]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    
    let t := Real.sqrt (1 + Real.sqrt (1 + a))
    have substitution : 2 * t + t = 6 := by
      
      rw [factorization] at h
      
      
      exact h
    have t_eq_two : t = 2 := by
      
      have h_three_t : 3 * t = 6 := by
        calc 3 * t
          = (2 + 1) * t := by norm_num
          _ = 2 * t + 1 * t := by rw [add_mul]
          _ = 2 * t + t := by rw [one_mul]
          _ = 6 := substitution
      linarith
    
    have back_substitute : a = 8 := by
      
      have h1 : Real.sqrt (1 + Real.sqrt (1 + a)) = 2 := t_eq_two
      
      have h2 : 1 + Real.sqrt (1 + a) = 4 := by
        have h_pos : 0 ≤ 1 + Real.sqrt (1 + a) := by
          apply add_nonneg
          · norm_num
          · exact Real.sqrt_nonneg _
        have h_two_pos : (0 : ℝ) ≤ 2 := by norm_num
        have h_sq : (1 + Real.sqrt (1 + a)) = 2 ^ 2 := by
          rw [Real.sqrt_eq_iff_eq_sq h_pos h_two_pos] at h1
          exact h1
        rw [h_sq]
        norm_num
      
      have h3 : Real.sqrt (1 + a) = 3 := by linarith [h2]
      
      have h4 : 1 + a = 9 := by
        have h_nonneg_inner : 0 ≤ 1 + a := by linarith [domain_constraint]
        have h_three_pos : (0 : ℝ) ≤ 3 := by norm_num
        have h_sq2 : (1 + a) = 3 ^ 2 := by
          rw [Real.sqrt_eq_iff_eq_sq h_nonneg_inner h_three_pos] at h3
          exact h3
        rw [h_sq2]
        norm_num
      
      linarith [h4]
    exact back_substitute
  · 
    intro ha
    
    rw [ha]
    
    
    
    
    
    have h1 : Real.sqrt 9 = 3 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
      norm_num
    have h2 : Real.sqrt 144 = 12 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 12)]
      norm_num
    have h3 : Real.sqrt 4 = 2 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have h4 : Real.sqrt 16 = 4 := by
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    
    have arith1 : (16 : ℝ) + 16 * 8 = 144 := by norm_num
    have arith2 : (1 : ℝ) + 8 = 9 := by norm_num
    have arith3 : (4 : ℝ) + 12 = 16 := by norm_num
    have arith4 : (1 : ℝ) + 3 = 4 := by norm_num
    rw [arith1, arith2, h2, h1, arith3, arith4, h4, h3]
    norm_num
