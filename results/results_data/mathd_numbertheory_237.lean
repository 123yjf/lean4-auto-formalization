import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

open Finset


theorem mathd_numbertheory_237 : (∑ i ∈ range 101, i) % 6 = 4 := by
  
  have h₁ : ∑ i ∈ range 101, i = 101 * (101 - 1) / 2 := by
    simpa using Finset.sum_range_id 101
  have h₂ : 101 * (101 - 1) / 2 = 5050 := by decide
  have hsum : ∑ i ∈ range 101, i = 5050 := by simpa [h₂] using h₁
  
  simpa [hsum] using (by decide : 5050 % 6 = 4)
