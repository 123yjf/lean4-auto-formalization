


import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic


theorem son_age_is_six : ∃ (s f : ℕ), f = 5 * s ∧ (f - 3) + (s - 3) = 30 ∧ s = 6 := by
  
  use 6, 30
