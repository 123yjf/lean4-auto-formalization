import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


theorem amc12b_2002_p7 :
    ∃ a b c : ℕ, a + 1 = b ∧ b + 1 = c ∧ a * b * c = 8 * (a + b + c) ∧ a^2 + b^2 + c^2 = 77 := by
  refine ⟨4, 5, 6, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
