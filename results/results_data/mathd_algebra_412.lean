import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith





theorem mathd_algebra_412 : ∃ x y : ℝ, x + y = 25 ∧ x - y = 11 ∧ x ≥ y ∧ x = 18 := by
  use 18, 7
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · rfl


lemma system_setup (x y : ℝ) : x + y = 25 ∧ x - y = 11 → x ≥ y := by
  intro ⟨h1, h2⟩
  linarith


lemma eliminate_y (x y : ℝ) : x + y = 25 → x - y = 11 → 2 * x = 36 := by
  intro h1 h2
  linarith


lemma solve_for_x (x : ℝ) : (2 : ℝ) * x = 36 → x = 18 := by
  intro h
  linarith


lemma verify_larger (x y : ℝ) : x + y = 25 → x = 18 → y = 7 ∧ x > y := by
  intro h1 h2
  constructor
  · linarith
  · linarith


lemma direct_formula : (25 + 11) / 2 = (18 : ℝ) := by
  norm_num


lemma solution_verification : (18 : ℝ) + 7 = 25 ∧ (18 : ℝ) - 7 = 11 := by
  constructor <;> norm_num


lemma uniqueness (x₁ y₁ x₂ y₂ : ℝ) :
  x₁ + y₁ = 25 ∧ x₁ - y₁ = 11 ∧ x₁ ≥ y₁ →
  x₂ + y₂ = 25 ∧ x₂ - y₂ = 11 ∧ x₂ ≥ y₂ →
  x₁ = x₂ ∧ y₁ = y₂ := by
  intro ⟨h1, h2, _⟩ ⟨h3, h4, _⟩
  constructor <;> linarith
