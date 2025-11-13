import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.NormNum



theorem mathd_algebra_484 : Real.logb 3 27 = 3 := by

  
  have step1 : Real.logb 3 27 = Real.log 27 / Real.log 3 := by
    rfl

  
  have step2 : (27 : ℝ) = 3^3 := by
    norm_num

  
  have step3 : Real.log (3^3) = 3 * Real.log 3 := by
    rw [Real.log_pow]
    norm_cast

  
  have step4 : (3 * Real.log 3) / Real.log 3 = 3 := by
    have h_nonzero : Real.log 3 ≠ 0 := by
      rw [Real.log_ne_zero]
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    field_simp [h_nonzero]

  
  have step5 : (3 : ℝ) > 0 ∧ 3 ≠ 1 ∧ (27 : ℝ) > 0 := by
    norm_num

  
  have step6 : (3 : ℝ)^3 = 27 := by
    norm_num

  
  have step7 : Real.logb 3 (3^3) = 3 := by
    have h_pos : (0 : ℝ) < 3 := by norm_num
    have h_ne_one : (3 : ℝ) ≠ 1 := by norm_num
    rw [← Real.rpow_natCast]
    exact Real.logb_rpow h_pos h_ne_one

  
  rw [← step6]
  exact step7
