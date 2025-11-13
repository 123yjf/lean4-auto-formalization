import Mathlib.Data.Nat.Basic
import Mathlib.Tactic





def amc10 (A M C : ℕ) : ℕ := 10000 * A + 1000 * M + 100 * C + 10
def amc12 (A M C : ℕ) : ℕ := 10000 * A + 1000 * M + 100 * C + 12


theorem amc12a_2003_p5 :
  ∃ A M C : ℕ,
    A ≥ 1 ∧ A ≤ 9 ∧ M ≤ 9 ∧ C ≤ 9 ∧
    amc10 A M C + amc12 A M C = 123422 ∧
    A + M + C = 14 := by
  use 6, 1, 7
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · norm_num  
  constructor
  · 
    unfold amc10 amc12
    norm_num
  · 
    norm_num


theorem amc12a_2003_p5_verification :
  amc10 6 1 7 + amc12 6 1 7 = 123422 := by
  unfold amc10 amc12
  norm_num
