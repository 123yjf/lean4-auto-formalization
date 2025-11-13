import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum












open Nat




theorem factorization_2001 : 2001 = 3 * 23 * 29 := by norm_num


theorem prime_3 : Nat.Prime 3 := prime_three


theorem product_check_1 : 3 * 667 = 2001 := by norm_num
theorem product_check_2 : 23 * 87 = 2001 := by norm_num
theorem product_check_3 : 29 * 69 = 2001 := by norm_num
theorem product_check_4 : 1 * 2001 = 2001 := by norm_num


theorem sum_triple_1 : 1 + 3 + 667 = 671 := by norm_num
theorem sum_triple_2 : 1 + 23 + 87 = 111 := by norm_num
theorem sum_triple_3 : 1 + 29 + 69 = 99 := by norm_num


theorem distinct_factors_1 : (1 : ℕ) ≠ 3 ∧ 3 ≠ 667 ∧ 1 ≠ 667 := by norm_num
theorem distinct_factors_2 : (1 : ℕ) ≠ 23 ∧ 23 ≠ 87 ∧ 1 ≠ 87 := by norm_num
theorem distinct_factors_3 : (1 : ℕ) ≠ 29 ∧ 29 ≠ 69 ∧ 1 ≠ 69 := by norm_num


theorem factor_667 : 667 = 23 * 29 := by norm_num
theorem factor_87 : 87 = 3 * 29 := by norm_num
theorem factor_69 : 69 = 3 * 23 := by norm_num


theorem sum_ordering : 671 > 111 ∧ 111 > 99 := by norm_num


theorem candidate_triple_works :
  let a := 1
  let b := 3
  let c := 667
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ a > 0 ∧ b > 0 ∧ c > 0 ∧ a * b * c = 2001 ∧ a + b + c = 671 := by
  norm_num






















