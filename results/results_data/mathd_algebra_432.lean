

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination


theorem mathd_algebra_432 (x : ℝ) : (x + 3) * (2 * x - 6) = 2 * x^2 - 18 := by
  
  
  have step1 : (x + 3) * (2 * x - 6) = x * (2 * x - 6) + 3 * (2 * x - 6) := by
    rw [add_mul]

  
  have step2 : x * (2 * x - 6) = 2 * x^2 - 6 * x := by
    rw [mul_sub]
    ring

  
  have step3 : 3 * (2 * x - 6) = 6 * x - 18 := by
    rw [mul_sub]
    ring

  
  have step4 : 2 * x^2 - 6 * x + (6 * x - 18) = 2 * x^2 - 18 := by
    ring

  
  rw [step1, step2, step3]
  exact step4
