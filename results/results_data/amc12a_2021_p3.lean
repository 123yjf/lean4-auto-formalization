import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith



open Nat





axiom problem_constraint : ∃ (x y : ℕ),
  x + y = 17402 ∧
  x % 10 = 0 ∧
  y = x / 10


axiom solution_values : ∃ (x y : ℕ),
  x = 15820 ∧
  y = 1582 ∧
  x + y = 17402 ∧
  x % 10 = 0 ∧
  y = x / 10


lemma calculation_x : 17402 * 10 / 11 = 15820 := by norm_num
lemma calculation_y : 15820 / 10 = 1582 := by norm_num
lemma calculation_sum : 15820 + 1582 = 17402 := by norm_num
lemma calculation_difference : 15820 - 1582 = 14238 := by norm_num


lemma verify_x_ends_in_zero : 15820 % 10 = 0 := by norm_num
lemma verify_y_equals_x_div_10 : 1582 = 15820 / 10 := by norm_num


theorem amc12a_2021_p3 :
  ∃ (x y : ℕ), x + y = 17402 ∧ x % 10 = 0 ∧ y = x / 10 ∧ x - y = 14238 :=
  ⟨15820, 1582, by norm_num, by norm_num, by norm_num, by norm_num⟩
