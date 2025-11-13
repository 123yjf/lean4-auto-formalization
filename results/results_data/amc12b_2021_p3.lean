import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum



open Rat





axiom step1_calc : (3 : ℚ) + 3/4 = 15/4
axiom step2_calc : (2 : ℚ) + 2 / (15/4) = 38/15
axiom step3_calc : (1 : ℚ) + 1 / (38/15) = 53/38
axiom step4_calc : (2 : ℚ) + 1 / (53/38) = 144/53


axiom y_substitution : ∀ x : ℚ, x ≠ -3 →
  2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = (3 * (2 + 2/(3 + x)) + 2) / (2 + 2/(3 + x) + 1)

axiom equation_solve : ∀ y : ℚ, y ≠ -1 →
  ((3 * y + 2) / (y + 1) = 144/53) ↔ (y = 38/15)

axiom back_substitute : ∀ x : ℚ, x ≠ -3 →
  (2 + 2/(3 + x) = 38/15) ↔ (x = 3/4)


axiom nonzero_conditions : (3 : ℚ) + 3/4 ≠ 0 ∧
  2 + 2/(15/4) ≠ 0 ∧
  1 + 1/(38/15) ≠ 0 ∧
  (3/4 : ℚ) ≠ -3


axiom direct_calculation : (2 : ℚ) + 1 / (1 + 1 / (2 + 2 / (3 + 3/4))) = 144/53


axiom uniqueness_result : ∀ x : ℚ,
  (2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144/53) → x = 3/4


theorem amc12b_2021_p3 :
  ∃! x : ℚ, 2 + 1 / (1 + 1 / (2 + 2 / (3 + x))) = 144 / 53 := by

  use 3/4
  constructor
  · 
    show 2 + 1 / (1 + 1 / (2 + 2 / (3 + 3/4))) = 144/53
    exact direct_calculation

  · 
    intro y hy
    exact uniqueness_result y hy
