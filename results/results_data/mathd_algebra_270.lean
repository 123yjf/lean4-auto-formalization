import Mathlib.Data.Rat.Init
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp





def f (x : ℚ) : ℚ := 1 / (x + (2 : ℚ))


theorem mathd_algebra_270 : f (f 1) = 3 / 7 := by
  
  have h1 : f 1 = 1 / 3 := by
    unfold f
    norm_num
  
  have h2 : f (1 / 3) = 3 / 7 := by
    unfold f
    field_simp
    norm_num
  
  rw [h1, h2]
