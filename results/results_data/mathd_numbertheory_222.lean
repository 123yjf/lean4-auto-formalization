import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring





theorem mathd_numbertheory_222 : ∃ b : ℕ,
  Nat.gcd 120 b = 8 ∧
  Nat.lcm 120 b = 3720 ∧
  b = 248 := by
  use 248
  constructor
  · decide  
  constructor
  · decide  
  · rfl     


lemma product_formula : ∀ a b : ℕ, a * b = Nat.gcd a b * Nat.lcm a b := by
  intro a b
  exact (Nat.gcd_mul_lcm a b).symm


lemma solve_for_b : 120 * 248 = 8 * 3720 := by
  norm_num


lemma factorization_120 : 120 = 2^3 * 3 * 5 := by
  norm_num


lemma factorization_248 : 248 = 2^3 * 31 := by
  norm_num


lemma verify_gcd : Nat.gcd 120 248 = 8 := by
  decide


lemma verify_lcm : Nat.lcm 120 248 = 3720 := by
  decide


lemma arithmetic_verification : 8 * 3720 = 29760 ∧ 29760 / 120 = 248 ∧ 2^3 * 3 * 5 * 31 = 3720 := by
  constructor <;> norm_num


lemma uniqueness (b : ℕ) : Nat.gcd 120 b = 8 ∧ Nat.lcm 120 b = 3720 → b = 248 := by
  intro ⟨h_gcd, h_lcm⟩
  
  have h_prod : 120 * b = Nat.gcd 120 b * Nat.lcm 120 b := product_formula 120 b
  
  have h_eq : 120 * b = 29760 := by
    calc 120 * b = Nat.gcd 120 b * Nat.lcm 120 b := h_prod
      _ = 8 * 3720 := by rw [h_gcd, h_lcm]
      _ = 29760 := by norm_num
  
  have h_check : 120 * 248 = 29760 := by norm_num
  rw [← h_check] at h_eq
  exact Nat.eq_of_mul_eq_mul_left (by norm_num : 120 > 0) h_eq
