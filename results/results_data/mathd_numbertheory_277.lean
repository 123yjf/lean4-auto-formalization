import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring



open Nat


theorem mathd_numbertheory_277 :
  ∃ (m n : ℕ), m > 0 ∧ n > 0 ∧ gcd m n = 6 ∧ lcm m n = 126 ∧ m + n = 60 := by
  
  use 18, 42
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · 
    rfl
  constructor
  · 
    rfl
  · 
    norm_num
