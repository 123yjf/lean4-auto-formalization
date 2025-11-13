import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum



theorem mathd_algebra_314 (n : ℤ) : (1 / 4 : ℚ) ^ (n + 1) * 2 ^ (2 * n) = 1 / 4 := by
  
  have step1 : (1 / 4 : ℚ) ^ (n + 1) * 2 ^ (2 * n) = (2 ^ (-2 : ℤ) : ℚ) ^ (n + 1) * 2 ^ (2 * n) := by
    congr 1
    norm_num

  
  have step2 : (2 ^ (-2 : ℤ) : ℚ) ^ (n + 1) = (2 : ℚ) ^ ((-2) * (n + 1)) := by
    rw [← zpow_mul]

  
  have step3 : (-2) * (n + 1) = -2 * n - 2 := by
    ring

  
  have step4 : (2 : ℚ) ^ (-2 * n - 2) * 2 ^ (2 * n) = (2 : ℚ) ^ ((-2 * n - 2) + 2 * n) := by
    have h_nonzero : (2 : ℚ) ≠ 0 := by norm_num
    rw [← zpow_add₀ h_nonzero]

  
  have step5 : (-2 * n - 2) + 2 * n = -2 := by
    ring

  
  have step6 : (2 : ℚ) ^ (-2 : ℤ) = 1 / 4 := by
    norm_num

  
  rw [step1, step2, step3, step4, step5, step6]
