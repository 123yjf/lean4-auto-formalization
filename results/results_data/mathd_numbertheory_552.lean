


import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


def f (x : ℕ) : ℕ := 12 * x + 7
def g (x : ℕ) : ℕ := 5 * x + 2
def h (x : ℕ) : ℕ := Nat.gcd (f x) (g x)


theorem mathd_numbertheory_552 :
  (∀ x : ℕ, x > 0 → h x = 1 ∨ h x = 11) ∧
  (∃ x : ℕ, x > 0 ∧ h x = 1) ∧
  (∃ x : ℕ, x > 0 ∧ h x = 11) ∧
  (1 + 11 = 12) := by
  constructor
  · 
    intro x hx
    
    have h_divides_11 : h x ∣ 11 := by
      
      
      
      have linear_comb : 5 * (12 * x + 7) = 12 * (5 * x + 2) + 11 := by ring
      have h_dvd_left : h x ∣ 12 * x + 7 := Nat.gcd_dvd_left _ _
      have h_dvd_right : h x ∣ 5 * x + 2 := Nat.gcd_dvd_right _ _
      have h_dvd_5left : h x ∣ 5 * (12 * x + 7) := dvd_mul_of_dvd_right h_dvd_left _
      have h_dvd_12right : h x ∣ 12 * (5 * x + 2) := dvd_mul_of_dvd_right h_dvd_right _
      rw [linear_comb] at h_dvd_5left
      
      
      
      have h_sub : 12 * (5 * x + 2) + 11 - 12 * (5 * x + 2) = 11 := by simp
      rw [← h_sub]
      exact Nat.dvd_sub h_dvd_5left h_dvd_12right
    
    have h_eq : h x = 1 ∨ h x = 11 := by
      
      exact (Nat.dvd_prime (by decide : Nat.Prime 11)).mp h_divides_11
    simp [h_eq]
  constructor
  · 
    use 1
    constructor
    · norm_num
    · 
      unfold h f g
      decide
  constructor
  · 
    use 4
    constructor
    · norm_num
    · 
      unfold h f g
      decide
  · 
    norm_num
