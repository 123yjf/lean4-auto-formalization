import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


theorem mathd_algebra_129 : ∃! a : ℝ, a ≠ 0 ∧ (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ - a⁻¹ = 1 := by
  
  have h1 : (8 : ℝ)⁻¹ / (4 : ℝ)⁻¹ = (1/8) / (1/4) := by
    simp only [inv_eq_one_div]

  
  have h2 : (1/8) / (1/4) = (1/2 : ℝ) := by
    field_simp
    norm_num

  
  have h3 : ∀ a : ℝ, a ≠ 0 → ((1/2 : ℝ) - a⁻¹ = 1 ↔ a⁻¹ = -(1/2)) := by
    intro a ha
    constructor
    · intro h
      linarith
    · intro h
      linarith

  
  have h4 : ∀ a : ℝ, a ≠ 0 → (a⁻¹ = -(1/2) ↔ a = -2) := by
    intro a ha
    constructor
    · intro h
      have : a = (a⁻¹)⁻¹ := (inv_inv a).symm
      rw [this, h]
      norm_num
    · intro h
      rw [h]
      norm_num

  
  use -2
  constructor
  · 
    constructor
    · norm_num 
    · rw [h1, h2]
      rw [h3 (-2) (by norm_num)]
      rw [h4 (-2) (by norm_num)]
  · 
    intro b hb
    cases' hb with hb_ne hb_eq
    rw [h1, h2] at hb_eq
    rw [h3 b hb_ne] at hb_eq
    rw [h4 b hb_ne] at hb_eq
    exact hb_eq
