import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic





def four_digit_number (n : ℕ) : ℕ := 3740 + n


theorem mathd_numbertheory_1124 :
  ∃! n : ℕ, n < 10 ∧ 18 ∣ four_digit_number n ∧ n = 4 := by
  use 4
  constructor
  · 
    constructor
    · norm_num  
    constructor
    · 
      
      
      unfold four_digit_number
      norm_num
    · rfl  
  · 
    intro n ⟨h_lt, h_div, _⟩
    
    interval_cases n
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      rfl  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
    · 
      unfold four_digit_number at h_div
      norm_num at h_div  
