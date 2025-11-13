import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic


lemma smallest_cube_and_fourth_power : ∀ m : ℕ, m > 1 → (∃ a : ℕ, m = a^3) → (∃ b : ℕ, m = b^4) → m ≥ 4096 := by
  intro m hm_gt_1 hm_cube hm_fourth
  
  
  obtain ⟨a, ha⟩ := hm_cube
  obtain ⟨b, hb⟩ := hm_fourth

  
  
  

  
  
  have h_2_12 : (2 : ℕ)^12 = 4096 := by norm_num

  
  
  have h_ge_2_12 : m ≥ 2^12 := by
    
    
    
    

    
    
    

    
    
    
    

    have h_4096 : (4096 : ℕ) = 2^12 := by norm_num
    rw [← h_4096]
    
    
    
    sorry

  exact h_ge_2_12


theorem mathd_numbertheory_296 :
  ∃ n : ℕ, n > 1 ∧
  (∃ a : ℕ, n = a^3) ∧
  (∃ b : ℕ, n = b^4) ∧
  (∀ m : ℕ, m > 1 → (∃ a : ℕ, m = a^3) → (∃ b : ℕ, m = b^4) → n ≤ m) ∧
  n = 4096 := by
  
  use 4096
  constructor
  · 
    norm_num
  constructor
  · 
    use 16
    norm_num
  constructor
  · 
    use 8
    norm_num
  constructor
  · 
    intro m hm_gt_1 hm_cube hm_fourth
    
    exact smallest_cube_and_fourth_power m hm_gt_1 hm_cube hm_fourth
  · 
    rfl
