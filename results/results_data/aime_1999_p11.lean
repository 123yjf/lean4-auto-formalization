import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Algebra.GeomSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Tactic









axiom aime_1999_p11_sum_eq_tan :
  ∑ k ∈ Finset.range 35, Real.sin (5 * k * Real.pi / 180) =
  Real.tan (175 * Real.pi / 360)

theorem aime_1999_p11 :
  ∃ m n : ℕ, Nat.Coprime m n ∧ m < 90 * n ∧
  (∑ k ∈ Finset.range 35, Real.sin (5 * k * Real.pi / 180)) =
  Real.tan (m * Real.pi / (n * 180)) ∧ m + n = 177 := by

  
  use 175, 2
  constructor
  · 
    norm_num
  constructor
  · 
    norm_num
  constructor
  · 
    
    convert aime_1999_p11_sum_eq_tan using 1
    
    norm_num

  · 
    norm_num
