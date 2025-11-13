import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum




axiom completing_square_circle (x y : ℝ) :
  x^2 + 8*x + y^2 - 6*y = 0 ↔ (x + 4)^2 + (y - 3)^2 = 25

theorem mathd_algebra_107 :
  ∃ (center_x center_y radius : ℝ), radius > 0 ∧ radius = 5 ∧
  ∀ (x y : ℝ), x^2 + 8*x + y^2 - 6*y = 0 ↔ (x - center_x)^2 + (y - center_y)^2 = radius^2 := by

  
  use -4, 3, 5

  constructor
  · 
    norm_num

  constructor
  · 
    rfl

  · 
    intro x y
    
    have h_axiom := completing_square_circle x y
    
    constructor
    · intro h
      
      have h_standard : (x + 4)^2 + (y - 3)^2 = 25 := h_axiom.mp h
      
      convert h_standard using 1
      · simp only [sub_neg_eq_add]
      · norm_num
    · intro h
      
      have h_standard : (x + 4)^2 + (y - 3)^2 = 25 := by
        convert h using 1
        · simp only [sub_neg_eq_add]
        · norm_num
      exact h_axiom.mpr h_standard
