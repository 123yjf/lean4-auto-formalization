import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

open Real




theorem amc12b_2020_p13 :
  sqrt (logb 2 6 + logb 3 6) = sqrt (logb 2 3) + sqrt (logb 3 2) := by

  
  have h1 : logb 2 6 = 1 + logb 2 3 := by
    calc logb 2 6
      = logb 2 (2 * 3) := by norm_num
      _ = logb 2 2 + logb 2 3 := logb_mul (by norm_num) (by norm_num)
      _ = 1 + logb 2 3 := by rw [logb_self_eq_one (by norm_num : 1 < (2 : ℝ))]

  have h2 : logb 3 6 = 1 + logb 3 2 := by
    calc logb 3 6
      = logb 3 (3 * 2) := by norm_num
      _ = logb 3 3 + logb 3 2 := logb_mul (by norm_num) (by norm_num)
      _ = 1 + logb 3 2 := by rw [logb_self_eq_one (by norm_num : 1 < (3 : ℝ))]

  
  have h3 : logb 3 2 = 1 / logb 2 3 := by
    rw [← inv_logb 2 3, one_div]

  
  have h4 : logb 2 6 + logb 3 6 = 2 + logb 2 3 + 1 / logb 2 3 := by
    rw [h1, h2, h3]
    ring

  
  have h5 : logb 2 3 * (1 / logb 2 3) = 1 := by
    have h_pos : 0 < logb 2 3 := logb_pos (by norm_num : 1 < (2 : ℝ)) (by norm_num)
    rw [mul_one_div, div_self (ne_of_gt h_pos)]

  
  rw [h4]
  have h_pos_log2_3 : 0 ≤ logb 2 3 := le_of_lt (logb_pos (by norm_num : 1 < (2 : ℝ)) (by norm_num))
  have h_pos_log3_2 : 0 ≤ 1 / logb 2 3 := by
    apply div_nonneg (by norm_num)
    exact le_of_lt (logb_pos (by norm_num : 1 < (2 : ℝ)) (by norm_num))

  
  have h_expand : (sqrt (logb 2 3) + sqrt (1 / logb 2 3))^2 =
    logb 2 3 + 2 * sqrt (logb 2 3) * sqrt (1 / logb 2 3) + 1 / logb 2 3 := by
    rw [add_pow_two, sq_sqrt h_pos_log2_3, sq_sqrt h_pos_log3_2]

  have h_sqrt_prod : sqrt (logb 2 3) * sqrt (1 / logb 2 3) = 1 := by
    rw [← sqrt_mul h_pos_log2_3 (1 / logb 2 3), h5, sqrt_one]

  
  have h_final : 2 + logb 2 3 + 1 / logb 2 3 = (sqrt (logb 2 3) + sqrt (1 / logb 2 3))^2 := by
    rw [h_expand]
    
    
    
    have h_eq : 2 * sqrt (logb 2 3) * sqrt (1 / logb 2 3) = 2 * 1 := by
      rw [mul_assoc, h_sqrt_prod]
    rw [h_eq, mul_one]
    ring

  rw [h_final, sqrt_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]
  rw [← h3]
