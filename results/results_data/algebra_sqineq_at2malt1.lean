import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith


lemma algebraic_proof (a : ℝ) : a * (2 - a) ≤ 1 := by
  
  have h1 : 1 - a * (2 - a) = (a - 1)^2 := by
    ring
  
  have h2 : (a - 1)^2 ≥ 0 := by
    exact sq_nonneg (a - 1)
  
  linarith [h1, h2]




lemma algebraic_manipulation (a : ℝ) : 1 - a * (2 - a) = (a - 1)^2 := by
  ring


lemma perfect_square_nonneg (a : ℝ) : (a - 1)^2 ≥ 0 := by
  exact sq_nonneg (a - 1)


lemma function_at_critical_point : (1 : ℝ) * (2 - 1) = 1 := by
  norm_num


theorem algebra_sqineq_at2malt1 (a : ℝ) : a * (2 - a) ≤ 1 := by
  exact algebraic_proof a
