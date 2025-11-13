





import Mathlib.Tactic



 theorem mathd_algebra_176 (x : ℝ) :
   (x + 1)^2 * x = x^3 + 2 * x^2 + x := by
  calc
    (x + 1)^2 * x = (x^2 + 2 * x + 1) * x := by ring
    _ = x^3 + 2 * x^2 + x := by ring
