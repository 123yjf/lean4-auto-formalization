import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum




theorem amc12b_2020_p2 :
  (100^2 - 7^2) / (70^2 - 11^2) * (70 - 11) * (70 + 11) / ((100 - 7) * (100 + 7)) = (1 : ℝ) := by

  
  
  
  
  

  
  have h1 : (100 : ℝ)^2 - 7^2 = 9951 := by norm_num
  have h2 : (70 : ℝ)^2 - 11^2 = 4779 := by norm_num
  have h3 : (70 : ℝ) - 11 = 59 := by norm_num
  have h4 : (70 : ℝ) + 11 = 81 := by norm_num
  have h5 : (100 : ℝ) - 7 = 93 := by norm_num
  have h6 : (100 : ℝ) + 7 = 107 := by norm_num

  
  rw [h1, h2, h3, h4, h5, h6]

  
  
  have h_factor1 : (9951 : ℝ) = 93 * 107 := by norm_num
  have h_factor2 : (4779 : ℝ) = 59 * 81 := by norm_num

  rw [h_factor1, h_factor2]

  
  
  have h_nonzero1 : (59 : ℝ) * 81 ≠ 0 := by norm_num
  have h_nonzero2 : (93 : ℝ) * 107 ≠ 0 := by norm_num

  field_simp [h_nonzero1, h_nonzero2]
  ring
