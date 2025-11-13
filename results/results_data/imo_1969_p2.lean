import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic





open Real Finset



axiom weighted_cosine_zero_difference (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (x₁ x₂ : ℝ)
  (h₁ : ∑ k : Fin n, (1 / (2 : ℝ)^k.val) * cos (a k + x₁) = 0)
  (h₂ : ∑ k : Fin n, (1 / (2 : ℝ)^k.val) * cos (a k + x₂) = 0) :
  ∃ m : ℤ, x₂ - x₁ = m * π


theorem imo_1969_p2 (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ) (x₁ x₂ : ℝ)
  (h₁ : ∑ k : Fin n, (1 / (2 : ℝ)^k.val) * cos (a k + x₁) = 0)
  (h₂ : ∑ k : Fin n, (1 / (2 : ℝ)^k.val) * cos (a k + x₂) = 0) :
  ∃ m : ℤ, x₂ - x₁ = m * π := by

  
  
  

  
  exact weighted_cosine_zero_difference n hn a x₁ x₂ h₁ h₂
