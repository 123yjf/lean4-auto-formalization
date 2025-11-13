import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum



theorem mathd_algebra_160 : ∃ (N x : ℝ),
  (N + x = (97 : ℝ)) ∧ (N + (5 : ℝ) * x = (265 : ℝ)) ∧ (N + (2 : ℝ) * x = (139 : ℝ)) := by
  
  use 55, 42
  
  constructor
  · norm_num  
  constructor
  · norm_num  
  · norm_num  
