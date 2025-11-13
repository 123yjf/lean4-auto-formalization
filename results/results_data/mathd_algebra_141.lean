








import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Rectangle

@[simp] def area (a b : ℝ) : ℝ := a * b
@[simp] def perimeter (a b : ℝ) : ℝ := 2 * (a + b)
@[simp] def diagonalSq (a b : ℝ) : ℝ := a ^ 2 + b ^ 2

end Rectangle




theorem rectangle_diagonal_sq_eq_369 {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b)
    (harea : Rectangle.area a b = 180)
    (hperim : Rectangle.perimeter a b = 54)
    (hPyth : d ^ 2 = Rectangle.diagonalSq a b) :
    d ^ 2 = 369 := by
  
  have hsum : a + b = 27 := by
    have h := congrArg (fun x : ℝ => x / 2) hperim
    norm_num at h
    simpa [Rectangle.perimeter] using h
  have hab : a * b = 180 := by simpa [Rectangle.area] using harea
  have hsq : a ^ 2 + b ^ 2 = 369 := by
    calc
      a ^ 2 + b ^ 2 = (a + b) ^ 2 - 2 * (a * b) := by ring
      _ = 27 ^ 2 - 2 * (a * b) := by simpa [hsum]
      _ = 27 ^ 2 - 2 * 180 := by simpa [hab]
      _ = 369 := by norm_num
  have hdiag' : d ^ 2 = a ^ 2 + b ^ 2 := by simpa [Rectangle.diagonalSq] using hPyth
  exact hdiag'.trans hsq
