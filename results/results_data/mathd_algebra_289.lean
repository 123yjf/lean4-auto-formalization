import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum




theorem mathd_algebra_289 :
  ∀ (m n k t : ℕ),
  Nat.Prime m → Nat.Prime n →
  k > t → t > 0 → k > 0 →
  k + t = m → k * t = n →
  m^n + n^m + k^t + t^k = 20 := by
  intro m n k t hm_prime hn_prime hk_gt_t ht_pos hk_pos hsum hprod

  
  
  have vieta_sum : k + t = m := hsum
  have vieta_prod : k * t = n := hprod

  
  
  have prime_factorization : k * t = n := vieta_prod
  have n_prime : Nat.Prime n := hn_prime
  
  
  have one_root_is_one : k = 1 ∨ t = 1 := by
    
    rw [← prime_factorization] at n_prime
    have h := Nat.prime_mul_iff.mp n_prime
    cases h with
    | inl h =>
      
      exact Or.inr h.2
    | inr h =>
      
      exact Or.inl h.2

  
  
  have t_eq_one_k_eq_n : t = 1 ∧ k = n := by
    cases one_root_is_one with
    | inl h =>
      
      
      exfalso
      rw [h] at hk_gt_t
      have : 1 ≤ t := ht_pos
      linarith
    | inr h =>
      
      
      rw [h] at vieta_prod
      simp at vieta_prod
      exact ⟨h, vieta_prod⟩

  
  
  have k_eq_two : k = 2 := by
    
    
    have k_prime : Nat.Prime k := by
      rw [t_eq_one_k_eq_n.2]
      exact hn_prime
    have m_eq_k_plus_one : m = k + 1 := by
      rw [← vieta_sum, t_eq_one_k_eq_n.1]
    have m_prime : Nat.Prime m := hm_prime
    
    cases k_prime.eq_two_or_odd' with
    | inl h =>
      
      exact h
    | inr h =>
      
      
      exfalso
      rw [m_eq_k_plus_one] at m_prime
      have k_ge_two : 2 ≤ k := k_prime.two_le
      have k_plus_one_ge_three : 3 ≤ k + 1 := by linarith
      have k_plus_one_even : Even (k + 1) := h.add_one
      have k_plus_one_gt_two : 2 < k + 1 := by linarith
      
      have not_prime_k_plus_one : ¬ Nat.Prime (k + 1) := by
        apply Nat.not_prime_of_dvd_of_lt k_plus_one_even.two_dvd
        · decide
        · exact k_plus_one_gt_two
      exact not_prime_k_plus_one m_prime

  
  
  have t_eq_one : t = 1 := t_eq_one_k_eq_n.1
  have k_eq_two_final : k = 2 := k_eq_two
  have n_eq_two : n = 2 := by
    rw [← t_eq_one_k_eq_n.2, k_eq_two_final]
  have m_eq_three : m = 3 := by
    rw [← vieta_sum, t_eq_one, k_eq_two_final]

  
  rw [m_eq_three, n_eq_two, k_eq_two_final, t_eq_one]
  norm_num
