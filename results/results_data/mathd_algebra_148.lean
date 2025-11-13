import Mathlib.Logic.ExistsUnique
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



theorem mathd_algebra_148 : ∃! c : ℝ, (fun x => c * x^3 - 9 * x + 3) 2 = 9 := by
  
  have h1 : ∀ c : ℝ, (fun x => c * x^3 - 9 * x + 3) 2 = c * 2^3 - 9 * 2 + 3 := by
    intro c
    simp

  
  have h2 : ∀ c : ℝ, c * 2^3 - 9 * 2 + 3 = 8 * c - 15 := by
    intro c
    ring

  
  have h3 : (8 : ℝ) * 3 - 15 = 9 := by
    norm_num

  
  use 3
  constructor
  · 
    simp only [h1 3, h2 3]
    exact h3
  · 
    intro c hc
    have hc_simplified : 8 * c - 15 = 9 := by
      rw [← h2 c, ← h1 c]
      exact hc
    linarith
