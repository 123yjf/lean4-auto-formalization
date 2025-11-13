import Mathlib


theorem mathd_algebra_142 :
  let B : ℚ × ℚ := (7, -1)
  let C : ℚ × ℚ := (-1, 7)
  let m : ℚ := (C.2 - B.2) / (C.1 - B.1)
  let b : ℚ := B.2 - m * B.1
  (B.2 = m * B.1 + b) ∧ (C.2 = m * C.1 + b) ∧ m = (-1 : ℚ) ∧ b = 6 ∧ m + b = 5 := by
  dsimp
  constructor
  · norm_num
  · constructor
    · norm_num
    · constructor
      · norm_num
      · constructor
        · norm_num
        · norm_num
