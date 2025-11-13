import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring



theorem mathd_numbertheory_100 : ∃! n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 := by

  
  have step1 : ∀ a b : ℕ, a * b = Nat.gcd a b * Nat.lcm a b := by
    intros a b
    exact (Nat.gcd_mul_lcm a b).symm

  
  have step2 : ∀ n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 → n * 40 = 10 * 280 := by
    intros n h
    have h1 := step1 n 40
    rw [h.1, h.2] at h1
    exact h1

  
  have step3 : (10 : ℕ) * 280 = 2800 := by
    norm_num

  
  have step4 : (2800 : ℕ) / 40 = 70 := by
    norm_num

  
  have step5 : Nat.gcd 70 40 = 10 := by
    rfl

  
  have step6 : Nat.lcm 70 40 = 280 := by
    rfl

  
  have step7 : 40 = 2^3 * 5 ∧ 70 = 2 * 5 * 7 := by
    constructor
    · norm_num
    · norm_num

  
  have step8 : ∀ n : ℕ, Nat.gcd n 40 = 10 ∧ Nat.lcm n 40 = 280 → n = 70 := by
    intros n h
    have h_gcd := h.1
    have h_lcm := h.2
    have h1 := step1 n 40
    rw [h_gcd, h_lcm] at h1
    rw [step3] at h1
    
    have h2 : n * 40 = 2800 := h1
    have h3 : 2800 = 70 * 40 := by norm_num
    have h4 : n * 40 = 70 * 40 := by rw [h2, h3]
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 40) h4

  
  use 70, ⟨step5, step6⟩, step8
