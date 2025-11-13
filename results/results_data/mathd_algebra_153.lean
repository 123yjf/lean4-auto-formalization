import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Rat.Floor


theorem mathd_algebra_153 :
  ⌊(10 : ℚ) * (1/3 : ℚ)⌋ + ⌊(100 : ℚ) * (1/3 : ℚ)⌋ + ⌊(1000 : ℚ) * (1/3 : ℚ)⌋ + ⌊(10000 : ℚ) * (1/3 : ℚ)⌋ = 3702 := by
  
  have h1 : ⌊(10 : ℚ) * (1/3 : ℚ)⌋ = 3 := by
    norm_num

  
  have h2 : ⌊(100 : ℚ) * (1/3 : ℚ)⌋ = 33 := by
    norm_num

  
  have h3 : ⌊(1000 : ℚ) * (1/3 : ℚ)⌋ = 333 := by
    norm_num

  
  have h4 : ⌊(10000 : ℚ) * (1/3 : ℚ)⌋ = 3333 := by
    norm_num

  
  rw [h1, h2, h3, h4]
  norm_num
