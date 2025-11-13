import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt


theorem abs_equation_iff_interval (x : ℝ) :
  |x - 1| + |x| + |x + 1| = x + 2 ↔ 0 ≤ x ∧ x ≤ 1 := by
  constructor
  · 
    intro h
    
    have lower_bound : |x - 1| + |x| + |x + 1| ≥ |x| + 2 := by
      
      have triangle : |x - 1| + |x + 1| ≥ |(x - 1) - (x + 1)| := by
        rw [← abs_neg (x + 1)]
        exact abs_add_le (x - 1) (-(x + 1))
      have simplify : |(x - 1) - (x + 1)| = 2 := by
        ring_nf
        simp [abs_two]
      rw [simplify] at triangle
      
      
      calc |x - 1| + |x| + |x + 1|
        = |x - 1| + |x + 1| + |x| := by ring
        _ ≥ 2 + |x| := add_le_add_right triangle |x|
        _ = |x| + 2 := by ring
    
    have abs_eq_x : |x| = x := by
      
      
      have : |x| + 2 ≤ x + 2 := by
        rw [← h]
        exact lower_bound
      have : |x| ≤ x := by linarith
      have : x ≤ |x| := le_abs_self x
      exact le_antisymm ‹|x| ≤ x› this
    constructor
    · 
      exact abs_eq_self.mp abs_eq_x
    · 
      
      have triangle_equality : (x - 1) * (x + 1) ≤ 0 := by
        
        have x_nonneg : 0 ≤ x := abs_eq_self.mp abs_eq_x
        
        have : |x - 1| + x + |x + 1| = x + 2 := by rwa [abs_eq_x] at h
        have : |x - 1| + |x + 1| = 2 := by linarith
        
        have pos_x_plus_1 : 0 < x + 1 := by linarith [x_nonneg]
        have : |x + 1| = x + 1 := abs_of_pos pos_x_plus_1
        rw [this] at ‹|x - 1| + |x + 1| = 2›
        have : |x - 1| = 2 - (x + 1) := by linarith [‹|x - 1| + (x + 1) = 2›]
        have : |x - 1| = 1 - x := by linarith [this]
        
        have : 0 ≤ 1 - x := by rw [← ‹|x - 1| = 1 - x›]; exact abs_nonneg _
        have x_le_one : x ≤ 1 := by linarith [this]
        
        
        calc (x - 1) * (x + 1)
          = x * x - 1 := by ring
          _ ≤ 1 - 1 := by
            have : x * x ≤ 1 := by
              have : x * x ≤ x * 1 := mul_le_mul_of_nonneg_left x_le_one (abs_eq_self.mp abs_eq_x)
              rw [mul_one] at this
              exact le_trans this x_le_one
            linarith [this]
          _ = 0 := by ring
      
      have bound_from_triangle : -1 ≤ x ∧ x ≤ 1 := by
        
        have x_sq_le_one : x * x ≤ 1 := by
          calc x * x
            = (x - 1) * (x + 1) + 1 := by ring
            _ ≤ 0 + 1 := by linarith [triangle_equality]
            _ = 1 := by ring
        
        have x_le_one_new : x ≤ 1 := by
          
          have x_nonneg : 0 ≤ x := abs_eq_self.mp abs_eq_x
          rw [← sq] at x_sq_le_one
          have : x ≤ √1 := Real.le_sqrt_of_sq_le x_sq_le_one
          rwa [Real.sqrt_one] at this
        constructor
        · 
          have x_nonneg : 0 ≤ x := abs_eq_self.mp abs_eq_x
          linarith [x_nonneg]
        · 
          exact x_le_one_new
      exact bound_from_triangle.2
  · 
    intro ⟨hx_nonneg, hx_le_one⟩
    
    
    have abs_x : |x| = x := abs_of_nonneg hx_nonneg
    have abs_x_plus_1 : |x + 1| = x + 1 := abs_of_pos (by linarith [hx_nonneg])
    have abs_x_minus_1 : |x - 1| = 1 - x := by
      have : x - 1 ≤ 0 := by linarith [hx_le_one]
      rw [abs_of_nonpos this]
      ring
    
    calc |x - 1| + |x| + |x + 1|
      = (1 - x) + x + (x + 1) := by rw [abs_x_minus_1, abs_x, abs_x_plus_1]
      _ = x + 2 := by ring
