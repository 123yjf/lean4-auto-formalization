import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic
import Mathlib.Tactic


theorem cyclic_sum_inequality (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
  a^2 / b + b^2 / c + c^2 / d + d^2 / a ≥ a + b + c + d := by
  
  
  
  
  have amgm1 : a^2 / b + b ≥ 2 * a := by
    have h_am_gm := Real.geom_mean_le_arith_mean2_weighted
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (div_nonneg (sq_nonneg a) (le_of_lt hb)) (le_of_lt hb)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have h_prod : (a^2 / b) ^ (1/2 : ℝ) * b ^ (1/2 : ℝ) = a := by
      rw [← Real.mul_rpow (div_nonneg (sq_nonneg a) (le_of_lt hb)) (le_of_lt hb)]
      have h_cancel : (a^2 / b) * b = a^2 := by field_simp [ne_of_gt hb]
      rw [h_cancel, ← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt ha)]
    rw [h_prod] at h_am_gm
    have h_rearrange : 1/2 * (a^2 / b) + 1/2 * b = (a^2 / b + b) / 2 := by ring
    rw [h_rearrange] at h_am_gm
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h_am_gm
    rw [mul_comm] at h_am_gm
    exact h_am_gm
  
  
  have amgm2 : b^2 / c + c ≥ 2 * b := by
    have h_am_gm := Real.geom_mean_le_arith_mean2_weighted
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (div_nonneg (sq_nonneg b) (le_of_lt hc)) (le_of_lt hc)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have h_prod : (b^2 / c) ^ (1/2 : ℝ) * c ^ (1/2 : ℝ) = b := by
      rw [← Real.mul_rpow (div_nonneg (sq_nonneg b) (le_of_lt hc)) (le_of_lt hc)]
      have h_cancel : (b^2 / c) * c = b^2 := by field_simp [ne_of_gt hc]
      rw [h_cancel, ← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hb)]
    rw [h_prod] at h_am_gm
    have h_rearrange : 1/2 * (b^2 / c) + 1/2 * c = (b^2 / c + c) / 2 := by ring
    rw [h_rearrange] at h_am_gm
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h_am_gm
    rw [mul_comm] at h_am_gm
    exact h_am_gm
  
  
  have amgm3 : c^2 / d + d ≥ 2 * c := by
    have h_am_gm := Real.geom_mean_le_arith_mean2_weighted
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (div_nonneg (sq_nonneg c) (le_of_lt hd)) (le_of_lt hd)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have h_prod : (c^2 / d) ^ (1/2 : ℝ) * d ^ (1/2 : ℝ) = c := by
      rw [← Real.mul_rpow (div_nonneg (sq_nonneg c) (le_of_lt hd)) (le_of_lt hd)]
      have h_cancel : (c^2 / d) * d = c^2 := by field_simp [ne_of_gt hd]
      rw [h_cancel, ← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hc)]
    rw [h_prod] at h_am_gm
    have h_rearrange : 1/2 * (c^2 / d) + 1/2 * d = (c^2 / d + d) / 2 := by ring
    rw [h_rearrange] at h_am_gm
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h_am_gm
    rw [mul_comm] at h_am_gm
    exact h_am_gm
  
  
  have amgm4 : d^2 / a + a ≥ 2 * d := by
    have h_am_gm := Real.geom_mean_le_arith_mean2_weighted
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2)
      (div_nonneg (sq_nonneg d) (le_of_lt ha)) (le_of_lt ha)
      (by norm_num : (1/2 : ℝ) + 1/2 = 1)
    have h_prod : (d^2 / a) ^ (1/2 : ℝ) * a ^ (1/2 : ℝ) = d := by
      rw [← Real.mul_rpow (div_nonneg (sq_nonneg d) (le_of_lt ha)) (le_of_lt ha)]
      have h_cancel : (d^2 / a) * a = d^2 := by field_simp [ne_of_gt ha]
      rw [h_cancel, ← Real.sqrt_eq_rpow, Real.sqrt_sq (le_of_lt hd)]
    rw [h_prod] at h_am_gm
    have h_rearrange : 1/2 * (d^2 / a) + 1/2 * a = (d^2 / a + a) / 2 := by ring
    rw [h_rearrange] at h_am_gm
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)] at h_am_gm
    rw [mul_comm] at h_am_gm
    exact h_am_gm
  
  
  have combination : a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) ≥ 
    2 * (a + b + c + d) := by
    have h_sum : a^2 / b + b + b^2 / c + c + c^2 / d + d + d^2 / a + a ≥ 
                 2 * a + 2 * b + 2 * c + 2 * d := by
      linarith [amgm1, amgm2, amgm3, amgm4]
    have h_rearrange : a^2 / b + b + b^2 / c + c + c^2 / d + d + d^2 / a + a = 
                       a^2 / b + b^2 / c + c^2 / d + d^2 / a + (a + b + c + d) := by ring
    have h_rhs : 2 * a + 2 * b + 2 * c + 2 * d = 2 * (a + b + c + d) := by ring
    rw [h_rearrange, h_rhs] at h_sum
    exact h_sum
  
  
  linarith [combination]
