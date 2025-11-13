import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum












open Complex Real




theorem numerical_fact_1 : (8 : ℂ) = 8 := by norm_num

theorem numerical_fact_2 : (2 : ℂ)^3 = 8 := by norm_num

theorem numerical_fact_3 : (84 : ℝ) = 4 * 21 := by norm_num

theorem numerical_fact_4 : (81 : ℝ) + 3 = 84 := by norm_num


theorem arithmetic_fact_1 : (-1 : ℝ) - 8 = -9 := by norm_num

theorem arithmetic_fact_2 : (-9 : ℝ)^2 = 81 := by norm_num

theorem arithmetic_fact_3 : (√3 : ℝ)^2 = 3 := by
  rw [sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]


theorem bound_example_1 : (84 : ℝ) > 36 := by norm_num

theorem bound_example_2 : (84 : ℝ) > 64 := by norm_num

theorem bound_example_3 : (84 : ℝ) > 32 := by norm_num


theorem power_fact_1 : (2 : ℝ)^2 = 4 := by norm_num

theorem power_fact_2 : (8 : ℝ)^2 = 64 := by norm_num

theorem power_fact_3 : (3 : ℝ) > 0 := by norm_num




















