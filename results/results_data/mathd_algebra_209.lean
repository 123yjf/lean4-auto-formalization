


import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic

theorem mathd_algebra_209 (f : ℝ → ℝ) (h : ℝ → ℝ)
  (h_inv : Function.LeftInverse h f ∧ Function.RightInverse h f)
  (h2 : h 2 = 10) (h10 : h 10 = 1) (h1 : h 1 = 2) :
  f (f 10) = 1 := by
  
  have f10_eq_2 : f 10 = 2 := by
    
    
    have h_left : Function.LeftInverse h f := h_inv.1
    
    
    
    have h_right : Function.RightInverse h f := h_inv.2
    
    rw [← h2]
    exact h_right 2
  
  have f2_eq_1 : f 2 = 1 := by
    
    have h_right : Function.RightInverse h f := h_inv.2
    
    rw [← h1]
    exact h_right 1
  
  calc f (f 10) = f 2 := by rw [f10_eq_2]
    _ = 1 := f2_eq_1
