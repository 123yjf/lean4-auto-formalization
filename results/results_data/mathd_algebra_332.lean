

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum


theorem mathd_algebra_332 (x y : ℝ) (h1 : x + y = 14) (h2 : x * y = 19) :
  x^2 + y^2 = 158 := by
  
  have identity : x^2 + y^2 = (x + y)^2 - 2 * (x * y) := by
    ring

  
  have substitution : (x + y)^2 - 2 * (x * y) = 14^2 - 2 * 19 := by
    rw [h1, h2]

  
  have computation : 14^2 - 2 * 19 = 158 := by
    norm_num

  
  rw [identity, substitution]
  norm_cast
