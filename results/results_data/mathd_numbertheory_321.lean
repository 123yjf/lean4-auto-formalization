import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Nat.ModEq


lemma verification : (160 * 1058) % 1399 = 1 := by
  norm_num


theorem mathd_numbertheory_321 : ∃! n : ℕ, n < 1399 ∧ (160 * n) % 1399 = 1 := by
  
  use 1058
  constructor
  · 
    constructor
    · 
      norm_num
    · 
      exact verification
  · 
    intro m hm
    
    
    
    
    
    have h1 : (160 * m) % 1399 = (160 * 1058) % 1399 := by
      rw [hm.2, verification]
    
    have h_coprime : Nat.Coprime 160 1399 := by
      norm_num [Nat.coprime_iff_gcd_eq_one]
    
    have h_mod_eq : m % 1399 = 1058 % 1399 := by
      
      have h_modeq : 160 * m ≡ 160 * 1058 [MOD 1399] := by
        rw [Nat.ModEq, h1]
      have h_gcd : Nat.gcd 1399 160 = 1 := by
        norm_num [Nat.gcd_comm]
      exact Nat.ModEq.cancel_left_of_coprime h_gcd h_modeq
    
    have hm_mod : m % 1399 = m := Nat.mod_eq_of_lt hm.1
    have h1058_mod : 1058 % 1399 = 1058 := by norm_num
    rw [hm_mod, h1058_mod] at h_mod_eq
    exact h_mod_eq




lemma inv_40_mod_1399 : (40 * 35) % 1399 = 1400 % 1399 := by
  norm_num


lemma inv_4_mod_1399 : (4 * 350) % 1399 = 1400 % 1399 := by
  norm_num


lemma mod_1400_1399 : 1400 % 1399 = 1 := by
  norm_num


lemma factorization_160 : 160 = 4 * 40 := by
  norm_num


lemma calculation_350_35 : (350 * 35) % 1399 = 1058 := by
  norm_num
