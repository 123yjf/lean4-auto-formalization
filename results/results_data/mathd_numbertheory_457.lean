import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic.Ring





theorem mathd_numbertheory_457 :
  (∀ n : ℕ, 80325 ∣ Nat.factorial n → n ≥ 17) ∧ (80325 ∣ Nat.factorial 17) := by
  constructor
  · intro n h
    by_contra h_not
    push_neg at h_not
    
    
    have h_fact : 80325 = 3^3 * 5^2 * 7 * 17 := by norm_num
    rw [h_fact] at h
    
    have h17_div_80325 : 17 ∣ 80325 := by
      rw [h_fact]
      exact dvd_mul_right 17 (3^3 * 5^2 * 7)
    
    have h17_div_nfact : 17 ∣ Nat.factorial n := dvd_trans h17_div_80325 h
    
    have h17_prime : Nat.Prime 17 := by decide
    have h17_le_n : 17 ≤ n := by
      rw [← Nat.Prime.dvd_factorial h17_prime]
      exact h17_div_nfact
    
    exact not_le.mpr h_not h17_le_n
  · 
    decide


lemma factorization_80325 : 80325 = 3^3 * 5^2 * 7 * 17 := by
  norm_num




lemma exponent_3_in_17_factorial : (3^3 : ℕ) ∣ Nat.factorial 17 := by
  
  decide


lemma exponent_5_in_17_factorial : (5^2 : ℕ) ∣ Nat.factorial 17 := by
  
  decide


lemma exponent_7_in_17_factorial : (7^1 : ℕ) ∣ Nat.factorial 17 := by
  exact Nat.dvd_factorial (by decide : 0 < 7) (by decide : 7 ≤ 17)


lemma exponent_17_in_17_factorial : (17^1 : ℕ) ∣ Nat.factorial 17 := by
  exact Nat.dvd_factorial (by decide : 0 < 17) (by decide : 17 ≤ 17)


lemma divides_17_factorial : 80325 ∣ Nat.factorial 17 := by
  
  decide


lemma minimality (n : ℕ) (hn : n < 17) : ¬(80325 ∣ Nat.factorial n) := by
  
  
  intro h
  rw [factorization_80325] at h
  
  have h17_div_80325 : 17 ∣ 80325 := by
    rw [factorization_80325]
    exact dvd_mul_right 17 (3^3 * 5^2 * 7)
  
  have h17_div_nfact : 17 ∣ Nat.factorial n := dvd_trans h17_div_80325 h
  
  have h17_prime : Nat.Prime 17 := by decide
  have h17_le_n : 17 ≤ n := by
    rw [← Nat.Prime.dvd_factorial h17_prime]
    exact h17_div_nfact
  
  exact not_le.mpr hn h17_le_n


lemma compute_floor_divisions :
  17 / 3 = 5 ∧ 17 / 9 = 1 ∧ 17 / 27 = 0 ∧
  17 / 5 = 3 ∧ 17 / 25 = 0 ∧
  17 / 7 = 2 ∧ 17 / 49 = 0 ∧
  17 / 17 = 1 := by
  norm_num
