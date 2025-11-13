import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.FieldTheory.Finite.Basic



open Nat


theorem fermat_little_theorem (p : ℕ) (hp : Nat.Prime p) (a : ℕ) : p ∣ (a^p - a) := by
  
  by_cases h : p ∣ a
  · 
    
    have h_pow : p ∣ a^p := h.pow (Nat.Prime.pos hp).ne'
    exact Nat.dvd_sub h_pow h
  · 
    
    haveI : Fact (Nat.Prime p) := ⟨hp⟩
    have h1 : (a : ZMod p) ^ p = (a : ZMod p) := ZMod.pow_card (a : ZMod p)
    
    have h2 : a ^ p ≡ a [MOD p] := by
      rw [← ZMod.eq_iff_modEq_nat]
      simp only [Nat.cast_pow]
      exact h1
    
    have h3 : a ≤ a ^ p := Nat.le_self_pow (Nat.Prime.pos hp).ne' a
    rw [← Nat.modEq_iff_dvd' h3]
    exact h2.symm
