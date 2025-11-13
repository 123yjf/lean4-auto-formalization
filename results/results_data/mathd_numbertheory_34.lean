import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_34 : ∃! x : ℕ, x < 100 ∧ (9 * x : ZMod 100) = 1 := by
  
  have h_gcd : Nat.gcd 9 100 = 1 := by
    decide

  have h_coprime : Nat.Coprime 9 100 := by
    rw [Nat.coprime_iff_gcd_eq_one]
    exact h_gcd

  have h_isUnit : IsUnit (9 : ZMod 100) := by
    apply (ZMod.isUnit_iff_coprime 9 100).mpr
    exact h_coprime

  
  have h_inv_val : (9 : ZMod 100)⁻¹ = 89 := by
    apply ZMod.inv_eq_of_mul_eq_one
    show (9 * 89 : ZMod 100) = 1
    decide

  
  have h_verification : (9 * 89 : ZMod 100) = 1 := by
    decide

  
  use 89
  constructor
  · constructor
    · norm_num
    · exact h_verification
  · intro y hy
    
    have h_eq : (9 * y : ZMod 100) = 1 := hy.2
    have h_y_is_inv : (y : ZMod 100) = (9 : ZMod 100)⁻¹ := by
      rw [← ZMod.inv_eq_of_mul_eq_one 100 (9 : ZMod 100) (y : ZMod 100)]
      exact h_eq
    rw [h_inv_val] at h_y_is_inv
    
    have h_y_lt : y < 100 := hy.1
    have h_89_lt : (89 : ℕ) < 100 := by norm_num
    have h_val_eq : (y : ZMod 100).val = (89 : ZMod 100).val := by
      rw [h_y_is_inv]
    rw [ZMod.val_natCast_of_lt h_y_lt] at h_val_eq
    
    have h_89_val : (89 : ZMod 100).val = 89 := ZMod.val_natCast_of_lt h_89_lt
    rw [h_89_val] at h_val_eq
    exact h_val_eq
