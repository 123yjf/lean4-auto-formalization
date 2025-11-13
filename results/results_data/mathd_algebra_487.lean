import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


theorem mathd_algebra_487 :
  ∃ (x₁ y₁ x₂ y₂ : ℝ),
    
    y₁ = x₁^2 ∧ x₁ + y₁ = 1 ∧
    
    y₂ = x₂^2 ∧ x₂ + y₂ = 1 ∧
    
    (x₁, y₁) ≠ (x₂, y₂) ∧
    
    Real.sqrt ((x₁ - x₂)^2 + (y₁ - y₂)^2) = Real.sqrt 10 := by

  
  let x₁ := (-1 + Real.sqrt 5) / 2
  let x₂ := (-1 - Real.sqrt 5) / 2
  let y₁ := (3 - Real.sqrt 5) / 2
  let y₂ := (3 + Real.sqrt 5) / 2

  use x₁, y₁, x₂, y₂

  constructor
  
  · have h_y1_eq : y₁ = x₁^2 := by
      
      unfold y₁ x₁
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    exact h_y1_eq

  constructor
  
  · have h_sum1 : x₁ + y₁ = 1 := by
      
      ring
    exact h_sum1

  constructor
  
  · have h_y2_eq : y₂ = x₂^2 := by
      
      unfold y₂ x₂
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      ring
    exact h_y2_eq

  constructor
  
  · have h_sum2 : x₂ + y₂ = 1 := by
      
      ring
    exact h_sum2

  constructor
  
  · have h_distinct : (x₁, y₁) ≠ (x₂, y₂) := by
      
      intro h
      have h_sqrt5_ne_zero : Real.sqrt 5 ≠ 0 := by norm_num
      have h_x_eq : x₁ = x₂ := by rw [Prod.mk_inj] at h; exact h.1
      unfold x₁ x₂ at h_x_eq
      have : Real.sqrt 5 = 0 := by linarith
      exact h_sqrt5_ne_zero this
    exact h_distinct

  
  · have h_distance : Real.sqrt ((x₁ - x₂)^2 + (y₁ - y₂)^2) = Real.sqrt 10 := by
      
      have h_diff_x : x₁ - x₂ = Real.sqrt 5 := by ring
      have h_diff_y : y₁ - y₂ = -Real.sqrt 5 := by ring
      rw [h_diff_x, h_diff_y]
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      norm_num
    exact h_distance
