import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real



theorem mathd_algebra_208 : Real.sqrt 1000000 - (1000000 : ℝ) ^ (1/3 : ℝ) = 900 := by
  
  
  have h1 : (1000000 : ℝ) = (10 : ℝ)^6 := by norm_num

  
  have h2 : Real.sqrt ((10 : ℝ)^6) = (10 : ℝ)^3 := by
    rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ (10 : ℝ)^3)]
    congr 1
    norm_num

  
  have h3 : ((10 : ℝ)^6) ^ (1/3 : ℝ) = (10 : ℝ)^2 := by
    rw [← Real.rpow_natCast (10 : ℝ) 6, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 10)]
    norm_num

  
  have h4 : (10 : ℝ)^3 - (10 : ℝ)^2 = 900 := by norm_num

  
  rw [h1, h2, h3, h4]
