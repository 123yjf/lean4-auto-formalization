import Mathlib.Data.Real.Basic
import Mathlib.Tactic


theorem mathd_algebra_513 {a b : ℝ} (h1 : 3 * a + 2 * b = 5) (h2 : a + b = 2) : a = 1 ∧ b = 1 := by
  have ha : a = 1 := by linarith [h1, h2]
  have hb : b = 1 := by linarith [h1, h2]
  exact ⟨ha, hb⟩
