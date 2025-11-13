import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic





theorem mathd_numbertheory_711 : ∃ (m n : ℕ),
  m > 0 ∧ n > 0 ∧
  Nat.gcd m n = 8 ∧
  Nat.lcm m n = 112 ∧
  (∀ (m' n' : ℕ), m' > 0 → n' > 0 → Nat.gcd m' n' = 8 → Nat.lcm m' n' = 112 → m + n ≤ m' + n') ∧
  m + n = 72 := by

  
  use 16, 56
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · 
    intro m' n' hm'_pos hn'_pos h_gcd' h_lcm'

    
    have h_product : m' * n' = 896 := by
      have := Nat.gcd_mul_lcm m' n'
      rw [h_gcd', h_lcm'] at this
      norm_num at this
      exact this.symm

    
    
    have hm'_div : 8 ∣ m' := by
      rw [← h_gcd']
      exact Nat.gcd_dvd_left m' n'
    have hn'_div : 8 ∣ n' := by
      rw [← h_gcd']
      exact Nat.gcd_dvd_right m' n'

    obtain ⟨a, ha⟩ := hm'_div
    obtain ⟨b, hb⟩ := hn'_div

    
    have h_ab : a * b = 14 := by
      have : (8 * a) * (8 * b) = 896 := by rw [← ha, ← hb]; exact h_product
      have : 64 * (a * b) = 896 := by rw [← this]; ring
      
      have h64_eq : 64 * 14 = 896 := by norm_num
      have : 64 * (a * b) = 64 * 14 := by rw [this, h64_eq]
      have h64_pos : (64 : ℕ) > 0 := by norm_num
      exact Nat.eq_of_mul_eq_mul_left h64_pos this

    
    
    
    have h_min_ab : a + b ≥ 9 := by
      
      
      sorry  

    
    rw [ha, hb]
    have : 8 * a + 8 * b = 8 * (a + b) := by ring
    rw [this]
    have : 8 * (a + b) ≥ 8 * 9 := Nat.mul_le_mul_left 8 h_min_ab
    have : 8 * 9 = 72 := by norm_num
    rw [this] at this
    exact this
  · norm_num  
