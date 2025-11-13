import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section


@[simp] def starOp (a b : ℝ) : ℝ := ((1 / b) - (1 / a)) / (a - b)

infixl:70 " ⋆ " => starOp

theorem mathd_algebra_139 : 3 ⋆ 11 = (1 : ℝ) / 33 := by
  
  unfold starOp
  norm_num
