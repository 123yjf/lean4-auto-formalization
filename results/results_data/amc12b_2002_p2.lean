import Mathlib.Tactic
import Mathlib.Algebra.Ring.Defs



theorem amc12b_2002_p2 (x : ℝ) :
  (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) + 1 = 3 * x - 1 := by
  
  
  
  
  
  

  
  have h_factor : (3 * x - 2) * (4 * x + 1) - (3 * x - 2) * (4 * x) =
                  (3 * x - 2) * ((4 * x + 1) - 4 * x) := by
    rw [← mul_sub]

  
  have h_simplify : (4 * x + 1) - 4 * x = 1 := by ring

  
  rw [h_factor, h_simplify]
  
  ring


theorem amc12b_2002_p2_at_4 :
  ((3 : ℝ) * 4 - 2) * (4 * 4 + 1) - (3 * 4 - 2) * (4 * 4) + 1 = 11 := by
  
  
  

  
  have h_eq : ((3 : ℝ) * 4 - 2) * (4 * 4 + 1) - (3 * 4 - 2) * (4 * 4) + 1 = 3 * 4 - 1 :=
    amc12b_2002_p2 4

  
  rw [h_eq]
  norm_num
