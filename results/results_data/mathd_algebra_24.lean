


import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

theorem mathd_algebra_24 : ∃ D : ℝ, 40 = 0.02 * D ∧ D = 2000 := by
  
  use 2000
  constructor
  · 
    
    
    norm_num
  · 
    rfl
