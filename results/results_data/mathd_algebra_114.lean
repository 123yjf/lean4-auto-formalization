import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


theorem mathd_algebra_114 : ((16 : ℝ) * ((8 : ℝ)^2)^(1/3 : ℝ))^(1/3 : ℝ) = 4 := by
  
  have h1 : (8 : ℝ)^2 = 64 := by norm_num

  
  have h2 : (64 : ℝ)^(1/3 : ℝ) = 4 := by
    have h2a : (4 : ℝ)^(3 : ℝ) = 64 := by norm_num
    have h2b : (1/3 : ℝ) = (3 : ℝ)⁻¹ := by norm_num
    rw [← h2a, h2b, Real.rpow_rpow_inv (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (3 : ℝ) ≠ 0)]

  
  have h3 : ((16 : ℝ) * 4)^(1/3 : ℝ) = 4 := by
    have h3a : (16 : ℝ) * 4 = 64 := by norm_num
    rw [h3a, h2]

  
  calc ((16 : ℝ) * ((8 : ℝ)^2)^(1/3 : ℝ))^(1/3 : ℝ)
    = ((16 : ℝ) * (64 : ℝ)^(1/3 : ℝ))^(1/3 : ℝ) := by rw [h1]
    _ = ((16 : ℝ) * 4)^(1/3 : ℝ) := by rw [h2]
    _ = 4 := by rw [h3]
