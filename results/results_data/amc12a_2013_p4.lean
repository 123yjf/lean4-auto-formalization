
import Mathlib.Tactic.Ring

set_option maxRecDepth 3000
set_option exponentiation.threshold 3000

theorem amc12a_2013_p4 : (2^2014 + 2^2012) / (2^2014 - 2^2012) = (5 : ℚ) / 3 := by
  
  have h1 : (2 : ℚ)^2014 = 2^2012 * 4 := by
    have : 2014 = 2012 + 2 := by norm_num
    rw [this, pow_add]
    norm_num
  
  calc ((2 : ℚ)^2014 + 2^2012) / (2^2014 - 2^2012)
    = (2^2012 * 4 + 2^2012) / (2^2012 * 4 - 2^2012) := by rw [h1]
    _ = (2^2012 * (4 + 1)) / (2^2012 * (4 - 1)) := by ring
    _ = (4 + 1) / (4 - 1) := by
      have h_ne_zero : (2 : ℚ)^2012 ≠ 0 := by
        simp only [ne_eq, pow_eq_zero_iff]
        norm_num
      rw [mul_div_mul_left _ _ h_ne_zero]
    _ = 5 / 3 := by norm_num
