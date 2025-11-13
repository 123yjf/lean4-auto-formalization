import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith





axiom amc12a_2002_p13_solution :
  ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a ≠ b ∧
  |a - 1/a| = 1 ∧ |b - 1/b| = 1 ∧ a + b = Real.sqrt 5

theorem amc12a_2002_p13 :
  ∃ a b : ℝ, a > 0 ∧ b > 0 ∧ a ≠ b ∧
  |a - 1/a| = 1 ∧ |b - 1/b| = 1 ∧ a + b = Real.sqrt 5 := by

  
  exact amc12a_2002_p13_solution
