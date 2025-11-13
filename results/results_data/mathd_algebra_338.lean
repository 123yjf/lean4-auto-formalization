import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith



theorem mathd_algebra_338 : ∃ a b c : ℚ,
  (3 * a + b + c = -3) ∧
  (a + 3 * b + c = 9) ∧
  (a + b + 3 * c = 19) ∧
  (a * b * c = -56) := by

  
  have rel1 : ∀ a b c : ℚ, (3 * a + b + c = -3) → (a + 3 * b + c = 9) → (b = a + 6) := by
    intros a b c h1 h2
    
    have h : -2 * a + 2 * b = 12 := by linear_combination h2 - h1
    
    linarith

  
  have rel2 : ∀ a b c : ℚ, (a + 3 * b + c = 9) → (a + b + 3 * c = 19) → (c = b + 5) := by
    intros a b c h2 h3
    
    have h : -2 * b + 2 * c = 10 := by linear_combination h3 - h2
    
    linarith

  
  have solve_a : ∀ a b c : ℚ, (3 * a + b + c = -3) → (b = a + 6) → (c = b + 5) → (a = -4) := by
    intros a b c h1 hb hc
    
    have h : 3 * a + (a + 6) + (a + 6 + 5) = -3 := by
      calc 3 * a + (a + 6) + (a + 6 + 5)
        = 3 * a + b + (b + 5) := by rw [hb]
        _ = 3 * a + b + c := by rw [hc]
        _ = -3 := h1
    
    linarith

  
  have solve_b : ∀ a b : ℚ, (a = -4) → (b = a + 6) → (b = 2) := by
    intros a b ha hb
    rw [ha] at hb
    linarith

  
  have solve_c : ∀ b c : ℚ, (b = 2) → (c = b + 5) → (c = 7) := by
    intros b c hb hc
    rw [hb] at hc
    linarith

  
  have product : ∀ a b c : ℚ, (a = -4) → (b = 2) → (c = 7) → (a * b * c = -56) := by
    intros a b c ha hb hc
    rw [ha, hb, hc]
    norm_num

  
  have verify : ∀ a b c : ℚ, (a = -4) → (b = 2) → (c = 7) →
    (3 * a + b + c = -3) ∧ (a + 3 * b + c = 9) ∧ (a + b + 3 * c = 19) := by
    intros a b c ha hb hc
    rw [ha, hb, hc]
    norm_num

  
  use -4, 2, 7
  constructor
  · 
    norm_num
  constructor
  · 
    norm_num
  constructor
  · 
    norm_num
  · 
    norm_num
