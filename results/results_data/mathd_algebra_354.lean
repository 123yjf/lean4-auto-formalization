

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination


def arithmetic_seq (a₁ d : ℝ) (n : ℕ) : ℝ := a₁ + (n - 1) * d


theorem mathd_algebra_354 (a₁ d : ℝ)
  (h₇ : arithmetic_seq a₁ d 7 = 30)
  (h₁₁ : arithmetic_seq a₁ d 11 = 60) :
  arithmetic_seq a₁ d 21 = 135 := by
  
  have formula : ∀ n, arithmetic_seq a₁ d n = a₁ + (n - 1) * d := by
    intro n
    rfl

  
  have eq₇ : a₁ + 6 * d = 30 := by
    rw [formula 7] at h₇
    norm_num at h₇
    exact h₇

  have eq₁₁ : a₁ + 10 * d = 60 := by
    rw [formula 11] at h₁₁
    norm_num at h₁₁
    exact h₁₁

  
  have d_val : d = 7.5 := by
    linear_combination (eq₁₁ - eq₇) / 4

  have a₁_val : a₁ = -15 := by
    linear_combination eq₇ - 6 * d_val

  
  have result : a₁ + 20 * d = 135 := by
    linear_combination a₁_val + 20 * d_val

  
  rw [formula]
  rw [a₁_val, d_val]
  norm_num
