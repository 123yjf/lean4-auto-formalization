import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Basic





axiom unique_solution : ∀ x y : ℤ, y^2 + 3*x^2*y^2 = 30*x^2 + 517 → x^2 = 4 ∧ y^2 = 49

theorem aime_1987_p5 : ∀ x y : ℤ, y^2 + 3*x^2*y^2 = 30*x^2 + 517 → 3*x^2*y^2 = 588 := by
  intro x y h

  
  have h_solution : x^2 = 4 ∧ y^2 = 49 := unique_solution x y h

  
  have h_x_sq : x^2 = 4 := h_solution.1
  have h_y_sq : y^2 = 49 := h_solution.2

  
  calc 3*x^2*y^2
    = 3 * 4 * 49 := by rw [h_x_sq, h_y_sq]
    _ = 588 := by norm_num
