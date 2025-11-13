import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


theorem mathd_algebra_263 : ∃! y : ℝ, Real.sqrt (19 + 3 * y) = 7 := by
  
  use 10
  constructor
  · 
    simp only [Function.comp_apply]
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 7)]
    norm_num
  · 
    intro y hy
    
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num : (0 : ℝ) < 7)] at hy
    
    
    norm_num at hy
    linarith
