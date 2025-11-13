import Mathlib.Tactic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.Int.ModEq


theorem mathd_numbertheory_293 : ∃! d : ℕ, d < 10 ∧ 11 ∣ (2000 + 10*d + 7) := by
  
  use 5
  constructor
  · 
    constructor
    · norm_num
    · 
      show 11 ∣ (2000 + 10*5 + 7)
      norm_num
  · 
    intro d' ⟨hd'_lt, hd'_div⟩
    interval_cases d'
    · 
      exfalso
      have : ¬(11 ∣ 2007) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2017) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2027) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2037) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2047) := by norm_num
      exact this hd'_div
    · 
      rfl
    · 
      exfalso
      have : ¬(11 ∣ 2067) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2077) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2087) := by norm_num
      exact this hd'_div
    · 
      exfalso
      have : ¬(11 ∣ 2097) := by norm_num
      exact this hd'_div
