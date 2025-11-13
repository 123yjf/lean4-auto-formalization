import Mathlib.Tactic




def g (x : ℝ) : ℝ := x - 3*x^2


theorem g_max_at_sixth : ∀ x : ℝ, g x ≤ g (1/6) := by
  intro x
  
  have h_g_sixth : g (1/6) = 1/12 := by
    unfold g
    norm_num

  rw [h_g_sixth]
  unfold g
  
  
  

  
  have h_complete_square : x - 3*x^2 = -3*(x - 1/6)^2 + 1/12 := by ring

  rw [h_complete_square]
  
  have h_neg_sq : -3*(x - 1/6)^2 ≤ 0 := by
    
    have h_sq_nonneg : 0 ≤ (x - 1/6)^2 := sq_nonneg _
    
    have h_neg_three : (-3 : ℝ) ≤ 0 := by norm_num
    
    calc -3 * (x - 1/6)^2
      ≤ 0 * (x - 1/6)^2 := by apply mul_le_mul_of_nonneg_right h_neg_three h_sq_nonneg
      _ = 0 := by simp

  
  calc -3*(x - 1/6)^2 + 1/12
    ≤ 0 + 1/12 := by apply add_le_add_right h_neg_sq
    _ = 1/12 := by simp


theorem g_at_sixth : g (1/6) = 1/12 := by
  unfold g
  norm_num


theorem quadratic_max_value : ∃ M : ℝ, M = 1/12 ∧ (∀ x : ℝ, g x ≤ M) ∧ (∃ x₀ : ℝ, g x₀ = M) := by
  use 1/12
  constructor
  · rfl
  constructor
  · intro x
    
    have h_max := g_max_at_sixth x
    rw [g_at_sixth] at h_max
    exact h_max
  · 
    use 1/6
    exact g_at_sixth
