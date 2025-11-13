import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith





theorem mathd_algebra_44 : ∃! p : ℝ × ℝ, p.1 = 9 - 2 * p.2 ∧ p.2 = 3 * p.1 + 1 ∧ p = (1, 4) := by
  use (1, 4)
  constructor
  · constructor
    · norm_num
    constructor
    · norm_num
    · rfl
  · intro ⟨s, t⟩ ⟨h1, h2, h3⟩
    
    
    
    
    
    have ht : t = 4 := by linarith [h1, h2]
    have hs : s = 1 := by linarith [h1, ht]
    rw [hs, ht]


lemma substitution_step (s t : ℝ) : s = 9 - 2 * t → (t = 3 * s + 1 ↔ t = 3 * (9 - 2 * t) + 1) := by
  intro h
  rw [h]


lemma simplify_substitution (t : ℝ) : t = 3 * (9 - 2 * t) + 1 ↔ t = 28 - 6 * t := by
  constructor
  · intro h
    ring_nf at h ⊢
    exact h
  · intro h
    ring_nf at h ⊢
    exact h


lemma solve_for_t (t : ℝ) : t = 28 - 6 * t ↔ 7 * t = 28 := by
  constructor
  · intro h
    linarith
  · intro h
    linarith


lemma t_equals_4 (t : ℝ) : 7 * t = 28 → t = 4 := by
  intro h
  linarith


lemma back_substitute_s (s t : ℝ) : s = 9 - 2 * t ∧ t = 4 → s = 1 := by
  intro ⟨h1, h2⟩
  rw [h2] at h1
  linarith


lemma verify_solution : (1 : ℝ) = 9 - 2 * 4 ∧ (4 : ℝ) = 3 * 1 + 1 := by
  constructor <;> norm_num


lemma uniqueness (s₁ t₁ s₂ t₂ : ℝ) :
  s₁ = 9 - 2 * t₁ ∧ t₁ = 3 * s₁ + 1 →
  s₂ = 9 - 2 * t₂ ∧ t₂ = 3 * s₂ + 1 →
  s₁ = s₂ ∧ t₁ = t₂ := by
  intro ⟨h1, h2⟩ ⟨h3, h4⟩
  
  constructor <;> linarith


lemma elimination_method : ∃ s t : ℝ, s = 9 - 2 * t ∧ t = 3 * s + 1 ∧ s = 1 ∧ t = 4 := by
  use 1, 4
  constructor
  · norm_num
  constructor
  · norm_num
  constructor <;> rfl
