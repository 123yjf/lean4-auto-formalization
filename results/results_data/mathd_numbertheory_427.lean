import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring




theorem mathd_numbertheory_427 :
  (∑ p ∈ (ArithmeticFunction.sigma 1 500).primeFactors, p) = 25 := by

  
  have step1_factorization : 500 = 2^2 * 5^3 := by
    norm_num

  
  have step2_sigma_2_2 : ArithmeticFunction.sigma 1 (2^2) = 7 := by
    rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

  
  have step3_sigma_5_3 : ArithmeticFunction.sigma 1 (5^3) = 156 := by
    have h5_prime : Nat.Prime 5 := by decide
    rw [ArithmeticFunction.sigma_one_apply_prime_pow h5_prime]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num

  
  have step4_sigma_500 : ArithmeticFunction.sigma 1 500 = 1092 := by
    rw [step1_factorization]
    have h_coprime : Nat.Coprime (2^2) (5^3) := by
      apply Nat.Coprime.pow
      decide
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_coprime, step2_sigma_2_2, step3_sigma_5_3]
    norm_num

  
  have step5_factorization_1092 : 1092 = 2^2 * 3 * 7 * 13 := by
    norm_num

  
  have step6_prime_factors : (1092 : ℕ).primeFactors = {2, 3, 7, 13} := by
    
    rw [step5_factorization_1092]
    
    have h1 : (2^2 * 3 * 7 * 13).primeFactors = (2^2 * 3).primeFactors ∪ (7 * 13).primeFactors := by
      
      have : 2^2 * 3 * 7 * 13 = (2^2 * 3) * (7 * 13) := by ring
      rw [this]
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    rw [h1]
    have h2 : (2^2 * 3).primeFactors = (2^2).primeFactors ∪ (3).primeFactors := by
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    have h3 : (7 * 13).primeFactors = (7).primeFactors ∪ (13).primeFactors := by
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    rw [h2, h3]
    
    have h4 : (2^2).primeFactors = {2} := by
      rw [Nat.primeFactors_pow_succ]
      exact Nat.Prime.primeFactors Nat.prime_two
    have h5 : (3).primeFactors = {3} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 3)
    have h6 : (7).primeFactors = {7} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 7)
    have h7 : (13).primeFactors = {13} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 13)
    rw [h4, h5, h6, h7]
    
    simp only [Finset.union_assoc]
    
    rfl

  
  have step7_sum : 2 + 3 + 7 + 13 = 25 := by
    norm_num

  
  rw [step4_sigma_500, step6_prime_factors]
  norm_num


theorem direct_verification :
  ArithmeticFunction.sigma 1 500 = 1092 ∧
  (1092 : ℕ).primeFactors = {2, 3, 7, 13} ∧
  2 + 3 + 7 + 13 = 25 := by
  constructor
  · 
    
    have h500 : 500 = 2^2 * 5^3 := by norm_num
    rw [h500]
    have h_coprime : Nat.Coprime (2^2) (5^3) := by
      apply Nat.Coprime.pow
      decide
    rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime h_coprime]
    
    have h2 : ArithmeticFunction.sigma 1 (2^2) = 7 := by
      rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    have h5 : ArithmeticFunction.sigma 1 (5^3) = 156 := by
      have h5_prime : Nat.Prime 5 := by decide
      rw [ArithmeticFunction.sigma_one_apply_prime_pow h5_prime]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      norm_num
    rw [h2, h5]
    norm_num
  constructor
  · 
    
    have h1092 : 1092 = 2^2 * 3 * 7 * 13 := by norm_num
    rw [h1092]
    
    have h1 : (2^2 * 3 * 7 * 13).primeFactors = (2^2 * 3).primeFactors ∪ (7 * 13).primeFactors := by
      have : 2^2 * 3 * 7 * 13 = (2^2 * 3) * (7 * 13) := by ring
      rw [this]
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    rw [h1]
    have h2 : (2^2 * 3).primeFactors = (2^2).primeFactors ∪ (3).primeFactors := by
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    have h3 : (7 * 13).primeFactors = (7).primeFactors ∪ (13).primeFactors := by
      apply Nat.primeFactors_mul
      · norm_num
      · norm_num
    rw [h2, h3]
    
    have h4 : (2^2).primeFactors = {2} := by
      rw [Nat.primeFactors_pow_succ]
      exact Nat.Prime.primeFactors Nat.prime_two
    have h5 : (3).primeFactors = {3} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 3)
    have h6 : (7).primeFactors = {7} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 7)
    have h7 : (13).primeFactors = {13} := by
      exact Nat.Prime.primeFactors (by decide : Nat.Prime 13)
    rw [h4, h5, h6, h7]
    
    simp only [Finset.union_assoc]
    rfl
  · 
    norm_num





theorem sigma_multiplicative (m n : ℕ) (hmn : m.Coprime n) :
  ArithmeticFunction.sigma 1 (m * n) = ArithmeticFunction.sigma 1 m * ArithmeticFunction.sigma 1 n := by
  
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn


theorem factorization_500 : 500 = 2^2 * 5^3 := by
  norm_num

theorem factorization_1092 : 1092 = 2^2 * 3 * 7 * 13 := by
  norm_num
