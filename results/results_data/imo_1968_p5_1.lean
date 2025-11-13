import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Real




axiom functional_equation_periodicity (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
  (h_func_eq : ∀ x : ℝ, f (x + a) = 1/2 + √(f x - (f x)^2)) :
  ∀ x : ℝ, f (x + 2*a) = f x

theorem imo_1968_p5 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
  (h_func_eq : ∀ x : ℝ, f (x + a) = 1/2 + √(f x - (f x)^2)) :
  ∃ b : ℝ, 0 < b ∧ ∀ x : ℝ, f (x + b) = f x := by

  
  have h_periodic := functional_equation_periodicity a ha f h_func_eq

  
  use 2*a
  constructor
  · 
    have h_pos : (0 : ℝ) < 2 := by norm_num
    exact mul_pos h_pos ha
  · 
    exact h_periodic
