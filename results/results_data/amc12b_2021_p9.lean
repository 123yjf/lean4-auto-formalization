import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

open Real


theorem amc12b_2021_p9 :
    (Real.logb 2 80) / (Real.logb 40 2) - (Real.logb 2 160) / (Real.logb 20 2) = 2 := by
  
  have h2pos : 1 < (2 : ℝ) := by norm_num
  have hlog2_ne : Real.log (2 : ℝ) ≠ 0 := (Real.log_pos h2pos).ne'
  have hlog40_ne : Real.log (40 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : 1 < (40 : ℝ))).ne'
  have hlog20_ne : Real.log (20 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : 1 < (20 : ℝ))).ne'
  have inv40_prod : (Real.logb 40 2) * (Real.logb 2 40) = 1 := by
    have hne : Real.log (2 : ℝ) * Real.log (40 : ℝ) ≠ 0 := mul_ne_zero hlog2_ne hlog40_ne
    calc
      (Real.logb 40 2) * (Real.logb 2 40)
          = (Real.log 2 / Real.log 40) * (Real.log 40 / Real.log 2) := by simp [Real.logb]
      _ = (Real.log 2 * Real.log 40) / (Real.log 2 * Real.log 40) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_mul_comm (Real.log 2) (Real.log 40) (Real.log 40) (Real.log 2)).symm
      _ = (Real.log 2 * Real.log 40) / (Real.log 2 * Real.log 40) := by simp [mul_comm]
      _ = 1 := by simpa [hne] using (div_self ((Real.log 2 * Real.log 40)))
  have inv20_prod : (Real.logb 20 2) * (Real.logb 2 20) = 1 := by
    have hne : Real.log (2 : ℝ) * Real.log (20 : ℝ) ≠ 0 := mul_ne_zero hlog2_ne hlog20_ne
    calc
      (Real.logb 20 2) * (Real.logb 2 20)
          = (Real.log 2 / Real.log 20) * (Real.log 20 / Real.log 2) := by simp [Real.logb]
      _ = (Real.log 2 * Real.log 20) / (Real.log 2 * Real.log 20) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (mul_div_mul_comm (Real.log 2) (Real.log 20) (Real.log 20) (Real.log 2)).symm
      _ = (Real.log 2 * Real.log 20) / (Real.log 2 * Real.log 20) := by simp [mul_comm]
      _ = 1 := by simpa [hne] using (div_self ((Real.log 2 * Real.log 20)))
  have inv40 : (Real.logb 40 2)⁻¹ = Real.logb 2 40 := by
    have hne : Real.logb 40 2 ≠ 0 := by
      intro h; simpa [h] using inv40_prod
    calc
      (Real.logb 40 2)⁻¹ = (Real.logb 40 2)⁻¹ * 1 := by simp
      _ = (Real.logb 40 2)⁻¹ * ((Real.logb 40 2) * (Real.logb 2 40)) := by simpa [inv40_prod]
      _ = ((Real.logb 40 2)⁻¹ * (Real.logb 40 2)) * (Real.logb 2 40) := by ring
      _ = 1 * (Real.logb 2 40) := by simp [hne]
      _ = Real.logb 2 40 := by simp
  have inv20 : (Real.logb 20 2)⁻¹ = Real.logb 2 20 := by
    have hne : Real.logb 20 2 ≠ 0 := by
      intro h; simpa [h] using inv20_prod
    calc
      (Real.logb 20 2)⁻¹ = (Real.logb 20 2)⁻¹ * 1 := by simp
      _ = (Real.logb 20 2)⁻¹ * ((Real.logb 20 2) * (Real.logb 2 20)) := by simpa [inv20_prod]
      _ = ((Real.logb 20 2)⁻¹ * (Real.logb 20 2)) * (Real.logb 2 20) := by ring
      _ = 1 * (Real.logb 2 20) := by simp [hne]
      _ = Real.logb 2 20 := by simp
  
  set x : ℝ := Real.logb 2 5
  have logb_2_2 : Real.logb 2 2 = 1 := by simpa using Real.logb_self_eq_one h2pos
  
  have h80 : Real.logb 2 80 = 4 + x := by
    have h2nz : (2 : ℝ) ≠ 0 := by norm_num
    have h5nz : (5 : ℝ) ≠ 0 := by norm_num
    have : (80 : ℝ) = (2 : ℝ) ^ 4 * 5 := by norm_num
    calc
      Real.logb 2 80 = Real.logb 2 ((2 : ℝ) ^ 4 * 5) := by simpa [this]
      _ = Real.logb 2 ((2 : ℝ) ^ 4) + Real.logb 2 5 :=
            (Real.logb_mul (by simpa using pow_ne_zero (4 : ℕ) h2nz) h5nz)
      _ = (4 : ℕ) * Real.logb 2 2 + x := by simpa [x] using (Real.logb_pow 2 (2 : ℝ) 4)
      _ = 4 + x := by simpa [logb_2_2]
  have h40 : Real.logb 2 40 = 3 + x := by
    have h2nz : (2 : ℝ) ≠ 0 := by norm_num
    have h5nz : (5 : ℝ) ≠ 0 := by norm_num
    have : (40 : ℝ) = (2 : ℝ) ^ 3 * 5 := by norm_num
    calc
      Real.logb 2 40 = Real.logb 2 ((2 : ℝ) ^ 3 * 5) := by simpa [this]
      _ = Real.logb 2 ((2 : ℝ) ^ 3) + Real.logb 2 5 :=
            (Real.logb_mul (by simpa using pow_ne_zero (3 : ℕ) h2nz) h5nz)
      _ = (3 : ℕ) * Real.logb 2 2 + x := by simpa [x] using (Real.logb_pow 2 (2 : ℝ) 3)
      _ = 3 + x := by simpa [logb_2_2]
  have h160 : Real.logb 2 160 = 5 + x := by
    have h2nz : (2 : ℝ) ≠ 0 := by norm_num
    have h5nz : (5 : ℝ) ≠ 0 := by norm_num
    have : (160 : ℝ) = (2 : ℝ) ^ 5 * 5 := by norm_num
    calc
      Real.logb 2 160 = Real.logb 2 ((2 : ℝ) ^ 5 * 5) := by simpa [this]
      _ = Real.logb 2 ((2 : ℝ) ^ 5) + Real.logb 2 5 :=
            (Real.logb_mul (by simpa using pow_ne_zero (5 : ℕ) h2nz) h5nz)
      _ = (5 : ℕ) * Real.logb 2 2 + x := by simpa [x] using (Real.logb_pow 2 (2 : ℝ) 5)
      _ = 5 + x := by simpa [logb_2_2]
  have h20 : Real.logb 2 20 = 2 + x := by
    have h2nz : (2 : ℝ) ≠ 0 := by norm_num
    have h5nz : (5 : ℝ) ≠ 0 := by norm_num
    have : (20 : ℝ) = (2 : ℝ) ^ 2 * 5 := by norm_num
    calc
      Real.logb 2 20 = Real.logb 2 ((2 : ℝ) ^ 2 * 5) := by simpa [this]
      _ = Real.logb 2 ((2 : ℝ) ^ 2) + Real.logb 2 5 :=
            (Real.logb_mul (by simpa using pow_ne_zero (2 : ℕ) h2nz) h5nz)
      _ = (2 : ℕ) * Real.logb 2 2 + x := by simpa [x] using (Real.logb_pow 2 (2 : ℝ) 2)
      _ = 2 + x := by simpa [logb_2_2]
  
  have t1 : (Real.logb 2 80) / (Real.logb 40 2) = (4 + x) * (3 + x) := by
    simpa [div_eq_mul_inv, inv40, h80, h40, mul_comm, mul_left_comm, mul_assoc]
  have t2 : (Real.logb 2 160) / (Real.logb 20 2) = (5 + x) * (2 + x) := by
    simpa [div_eq_mul_inv, inv20, h160, h20, mul_comm, mul_left_comm, mul_assoc]
  
  simpa [t1, t2] using by
    ring
