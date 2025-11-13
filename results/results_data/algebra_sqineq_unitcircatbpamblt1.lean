


import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic


theorem algebra_sqineq_unitcircatbpamblt1 (a b : ℝ) (h_unit : a^2 + b^2 = 1) :
  (a + b)^2 ≤ 2 := by
  
  

  
  have expansion : (a + b)^2 = a^2 + 2*a*b + b^2 := by
    
    ring

  
  have unit_constraint : a^2 + b^2 = 1 := h_unit

  
  have cross_term_bound : a*b ≤ (a^2 + b^2) / 2 := by
    
    
    
    
    have h : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
    
    
    have expand : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
    
    
    rw [expand] at h
    
    
    have : 2*a*b ≤ a^2 + b^2 := by linarith [h]
    
    
    linarith [this]

  
  have final_bound : (a + b)^2 = 1 + 2*a*b ∧ 2*a*b ≤ 2 * ((a^2 + b^2) / 2) := by
    constructor
    
    
    · have expand : (a + b)^2 = a^2 + 2*a*b + b^2 := by ring
      rw [expand]
      rw [← h_unit]
      ring
    
    
    · have cross_bound : a*b ≤ (a^2 + b^2) / 2 := by
        
        have h : (a - b)^2 ≥ 0 := sq_nonneg (a - b)
        have expand : (a - b)^2 = a^2 - 2*a*b + b^2 := by ring
        rw [expand] at h
        have : 2*a*b ≤ a^2 + b^2 := by linarith [h]
        linarith [this]
      
      
      have : 2*a*b ≤ a^2 + b^2 := by linarith [cross_bound]
      
      
      have simplify : 2 * ((a^2 + b^2) / 2) = a^2 + b^2 := by ring
      
      rw [simplify]
      exact this

  
  rw [expansion, unit_constraint] at *
  have : 2*a*b ≤ 1 := by
    have : a*b ≤ 1/2 := by linarith [cross_term_bound, unit_constraint]
    linarith
  linarith
