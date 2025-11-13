import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum.Basic




def f (x : ℝ) : ℝ := (5 : ℝ) * x + (4 : ℝ)


theorem mathd_algebra_171 : f 1 = 9 := by
  
  unfold f
  
  norm_num
