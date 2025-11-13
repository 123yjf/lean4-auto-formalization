import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


theorem mathd_algebra_362 :
  ∃ (a b : ℝ),
    a^2 * b^3 = 32/27 ∧
    a / b^3 = 27/4 ∧
    a + b = 8/3 := by

  
  use 2, 2/3

  constructor
  
  · 
    have h_a : (2 : ℝ) = 2 := rfl
    have h_b : (2/3 : ℝ) = 2/3 := rfl
    have h_calc : (2 : ℝ)^2 * (2/3)^3 = 32/27 := by
      
      norm_num
    exact h_calc

  constructor
  
  · 
    have h_calc : (2 : ℝ) / (2/3)^3 = 27/4 := by
      
      norm_num
    exact h_calc

  
  · 
    have h_calc : (2 : ℝ) + 2/3 = 8/3 := by
      
      norm_num
    exact h_calc
