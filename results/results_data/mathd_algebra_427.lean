





import Mathlib.Data.Real.Basic
import Mathlib.Tactic


theorem mathd_algebra_427 {x y z : ℝ}
  (h1 : 3 * x + y = 17) (h2 : 5 * y + z = 14) (h3 : 3 * x + 5 * z = 41) :
  x + y + z = 12 := by
  
  have h6 : 6 * (x + y + z) = 72 := by
    calc
      6 * (x + y + z) = (3 * x + y) + (5 * y + z) + (3 * x + 5 * z) := by ring
      _ = 17 + 14 + 41 := by simpa [h1, h2, h3]
      _ = 72 := by norm_num
  
  have h6ne : (6 : ℝ) ≠ 0 := by norm_num
  have hx : x + y + z = 72 / 6 :=
    (eq_div_iff_mul_eq h6ne).2 (by simpa [mul_comm] using h6)
  simpa using (hx.trans (by norm_num : ((72 : ℝ) / 6) = 12))
