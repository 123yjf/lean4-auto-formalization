import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

open Finset


theorem mathd_numbertheory_239 : (∑ i ∈ range 13, i) % 4 = 2 := by
  
  have h₁ : ∑ i ∈ range 13, i = 13 * (13 - 1) / 2 := by
    simpa using Finset.sum_range_id 13
  have h₂ : 13 * (13 - 1) / 2 = 78 := by decide
  have hsum : ∑ i ∈ range 13, i = 78 := by simpa [h₂] using h₁
  
  simpa [hsum] using (by decide : 78 % 4 = 2)
