import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ChineseRemainder


theorem last_three_digits_sum :
  let last_three := (5^100) % 1000
  let d1 := last_three / 100
  let d2 := (last_three % 100) / 10
  let d3 := last_three % 10
  d1 + d2 + d3 = 13 := by
  
  have h1 : (5^100) % 125 = 0 := by
    
    have h_125 : 125 = 5^3 := rfl
    rw [h_125]
    rw [← Nat.dvd_iff_mod_eq_zero]
    
    exact pow_dvd_pow 5 (by decide : 3 ≤ 100)

  
  have h2 : (5^100) % 8 = 1 := by
    
    have h_5_sq : (5^2) % 8 = 1 := by decide
    
    calc (5^100) % 8
      = (5^(2 * 50)) % 8 := by rfl
      _ = ((5^2)^50) % 8 := by rw [pow_mul]
      _ = (1^50) % 8 := by rw [Nat.pow_mod, h_5_sq]
      _ = 1 % 8 := by rw [one_pow]
      _ = 1 := by decide

  
  have h3 : (5^100) % 1000 = 625 := by
    
    
    have h_5_10 : (5^10) % 1000 = 625 := by decide
    
    calc (5^100) % 1000
      = ((5^10)^10) % 1000 := by rw [← pow_mul]
      _ = (625^10) % 1000 := by rw [Nat.pow_mod, h_5_10]
      _ = 625 := by decide

  
  have h4 : 625 / 100 = 6 ∧ (625 % 100) / 10 = 2 ∧ 625 % 10 = 5 := by
    constructor
    · decide  
    constructor
    · decide  
    · decide  

  
  
  simp only [h3, h4.1, h4.2.1, h4.2.2]
