import Mathlib.Tactic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.GCD.Basic


theorem induction_12dvd4expnp1p20 (n : ℕ) : 12 ∣ (4^(n+1) + 20) := by
  
  

  
  have h4 : 4 ∣ (4^(n+1) + 20) := by
    apply dvd_add
    · 
      apply dvd_pow
      norm_num
      simp
    · 
      norm_num

  
  have h3 : 3 ∣ (4^(n+1) + 20) := by
    
    
    have h1 : 4 % 3 = 1 := by norm_num
    have h2 : 4^(n+1) % 3 = 1 := by
      rw [Nat.pow_mod]
      rw [h1]
      simp [Nat.one_pow]
    have h3 : 20 % 3 = 2 := by norm_num
    have h4 : (4^(n+1) + 20) % 3 = 0 := by
      rw [Nat.add_mod, h2, h3]
    exact Nat.dvd_iff_mod_eq_zero.mpr h4

  
  have hcoprime : Nat.Coprime 4 3 := by
    norm_num [Nat.Coprime, Nat.gcd]

  
  
  have h12 : 4 * 3 ∣ (4^(n+1) + 20) := by
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd hcoprime h4 h3

  
  have h12_final : 12 ∣ (4^(n+1) + 20) := by
    convert h12

  exact h12_final
