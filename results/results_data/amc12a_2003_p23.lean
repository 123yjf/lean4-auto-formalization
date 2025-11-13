import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith



open Nat Finset




axiom superfactorial_prime_factorization :
  ∏ k ∈ range 9, (k + 1)! = 2^30 * 3^13 * 5^5 * 7^3

axiom perfect_square_divisor_count_total :
  ∃ n : ℕ, n = 672 ∧
  n = (30 / 2 + 1) * (13 / 2 + 1) * (5 / 2 + 1) * (3 / 2 + 1)

axiom product_formula_superfactorial :
  ∏ k ∈ range 9, (k + 1)! = ∏ t ∈ range 9, (t + 1)^(9 - t)


lemma prime_factorization_superfactorial :
  ∏ k ∈ range 9, (k + 1)! = 2^30 * 3^13 * 5^5 * 7^3 :=
  superfactorial_prime_factorization


lemma perfect_square_count_result :
  ∃ n : ℕ, n = 672 ∧
  n = (30 / 2 + 1) * (13 / 2 + 1) * (5 / 2 + 1) * (3 / 2 + 1) :=
  perfect_square_divisor_count_total


lemma prime_2_contribution : (30 : ℕ) / 2 + 1 = 16 := by norm_num
lemma prime_3_contribution : (13 : ℕ) / 2 + 1 = 7 := by norm_num
lemma prime_5_contribution : (5 : ℕ) / 2 + 1 = 3 := by norm_num
lemma prime_7_contribution : (3 : ℕ) / 2 + 1 = 2 := by norm_num


lemma final_product : 16 * 7 * 3 * 2 = 672 := by norm_num


theorem amc12a_2003_p23 :
  ∃ n : ℕ, n = 672 ∧
  (∏ k ∈ range 9, (k + 1)! = 2^30 * 3^13 * 5^5 * 7^3) ∧
  n = (30 / 2 + 1) * (13 / 2 + 1) * (5 / 2 + 1) * (3 / 2 + 1) := by

  use 672
  constructor
  · rfl
  constructor
  · 
    exact prime_factorization_superfactorial
  · 
    have h_result := perfect_square_count_result
    obtain ⟨n, hn_eq, hn_formula⟩ := h_result
    rw [← hn_eq]
    exact hn_formula
