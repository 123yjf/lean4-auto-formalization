

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


theorem mathd_algebra_33 (x y z : ℝ) (hx : x ≠ 0) (h1 : 2 * x = 5 * y) (h2 : 7 * y = 10 * z) :
  z / x = 7 / 25 := by
  
  have step1 : y = (2 / 5) * x := by
    linarith [h1]

  
  have step2 : z = (7 / 25) * x := by
    linarith [step1, h2]

  
  have step3 : z / x = 7 / 25 := by
    rw [step2]
    field_simp [hx]
    ring

  exact step3
