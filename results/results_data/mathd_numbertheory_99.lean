

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.Ring.Basic

theorem mathd_numbertheory_99 : ∃! n : ZMod 47, 2 * n = 15 ∧ (n.val < 47) := by
  
  have h1 : IsUnit (2 : ZMod 47) := by
    exact (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 47)).isUnit

  
  have h2 : (2 : ZMod 47)⁻¹ = 24 := by
    have h_check : (2 : ZMod 47) * 24 = 1 := by decide
    exact ZMod.inv_eq_of_mul_eq_one 47 2 24 h_check

  
  have h3 : ∀ n : ZMod 47, 2 * n = 15 → n = 24 * 15 := by
    intro n hn
    have : n = (2 : ZMod 47)⁻¹ * (2 * n) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit 2 h1, one_mul]
    rw [this, hn, h2]

  
  have h4 : (24 * 15 : ZMod 47) = 31 := by
    decide

  
  have h5 : 2 * (31 : ZMod 47) = 15 := by
    decide

  
  use 31
  constructor
  · constructor
    · exact h5
    · exact ZMod.val_lt 31
  · intro n hn
    exact h3 n hn.1
