import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith


theorem not_equiv_both_even_iff_eight_div_sum_squares :
  ¬ ∀ (a b : ℤ), (Even a ∧ Even b) ↔ (8 ∣ a^2 + b^2) := by
  
  push_neg
  use 2, 0
  
  
  
  left
  constructor
  · 
    constructor
    · exact even_two
    · exact Even.zero
  · 
    simp only [pow_two, zero_pow, add_zero]
    
    norm_num
