import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


theorem mathd_algebra_275 (x : ℝ) (h : ((11 : ℝ)^((1 : ℝ)/4))^(3*x - 3) = 1/5) :
  ((11 : ℝ)^((1 : ℝ)/4))^(6*x + 2) = 121/25 := by
  
  let a := (11 : ℝ)^((1 : ℝ)/4)
  have h_given : a^(3*x - 3) = 1/5 := by
    simp only [a]
    exact h

  
  have h_linear : 6*x + 2 = 2*(3*x - 3) + 8 := by
    ring

  
  have h_exponent : a^(6*x + 2) = (a^(3*x - 3))^2 * a^8 := by
    rw [h_linear]
    have ha_pos : 0 < a := by
      simp only [a]
      apply Real.rpow_pos_of_pos
      norm_num
    rw [Real.rpow_add ha_pos]
    congr 1
    · rw [mul_comm, Real.rpow_mul (le_of_lt ha_pos)]
      norm_num
    · norm_cast

  
  have h_compute : a^8 = 121 := by
    simp only [a]
    have h1 : ((11 : ℝ)^((1 : ℝ)/4))^(8 : ℕ) = (11 : ℝ)^((1 : ℝ)/4 * 8) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul]
      · norm_num
      · norm_num
    rw [h1]
    norm_num

  
  calc ((11 : ℝ)^((1 : ℝ)/4))^(6*x + 2)
    = a^(6*x + 2) := by simp only [a]
    _ = (a^(3*x - 3))^2 * a^8 := h_exponent
    _ = (1/5)^2 * 121 := by rw [h_given, h_compute]
    _ = 1/25 * 121 := by norm_num
    _ = 121/25 := by norm_num
