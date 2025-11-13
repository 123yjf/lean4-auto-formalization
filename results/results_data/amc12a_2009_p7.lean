import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum




def arithmetic_seq (a₁ d : ℝ) (n : ℕ) : ℝ := a₁ + (n - 1) * d


theorem amc12a_2009_p7 :
  ∃ (x : ℝ) (n : ℕ),
    
    (5*x - 11) - (2*x - 3) = (3*x + 1) - (5*x - 11) ∧
    
    arithmetic_seq (2*x - 3) ((5*x - 11) - (2*x - 3)) n = 2009 ∧
    
    n = 502 := by

  
  
  
  
  

  use 4, 502

  constructor
  
  · 
    
    
    
    norm_num

  constructor
  
  · 
    
    
    
    

    
    have h_a1 : (2 * 4 - 3 : ℝ) = 5 := by norm_num
    have h_d : ((5 * 4 - 11) - (2 * 4 - 3) : ℝ) = 4 := by norm_num

    
    rw [arithmetic_seq]
    
    simp only [h_a1]
    
    
    have h_d_simp : ((5 * 4 - 11) - 5 : ℝ) = 4 := by norm_num
    rw [h_d_simp]
    
    
    norm_num

  
  · rfl
