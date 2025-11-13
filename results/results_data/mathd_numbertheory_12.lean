

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_12 :
  Finset.card ((Finset.range 86).filter (fun n => 15 ≤ n ∧ n ≤ 85 ∧ 20 ∣ n)) = 4 := by
  
  
  have step1 : Finset.card ((Finset.range 86).filter (fun n => 20 ∣ n)) = 5 := by
    decide

  
  have step2 : Finset.card ((Finset.range 15).filter (fun n => 20 ∣ n)) = 1 := by
    decide

  
  have step3 : Finset.card ((Finset.range 86).filter (fun n => 15 ≤ n ∧ n ≤ 85 ∧ 20 ∣ n)) =
               Finset.card ((Finset.range 86).filter (fun n => 20 ∣ n)) -
               Finset.card ((Finset.range 15).filter (fun n => 20 ∣ n)) := by
    
    
    have h1 : (Finset.range 86).filter (fun n => 15 ≤ n ∧ n ≤ 85 ∧ 20 ∣ n) =
              (Finset.range 86).filter (fun n => 20 ∣ n) \ (Finset.range 15).filter (fun n => 20 ∣ n) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_range]
      constructor
      · intro ⟨hn_lt, h15, h85, hdiv⟩
        exact ⟨⟨hn_lt, hdiv⟩, fun ⟨hn_lt', _⟩ => Nat.not_lt.mpr h15 hn_lt'⟩
      · intro ⟨⟨hn_lt, hdiv⟩, hnot⟩
        refine ⟨hn_lt, ?_, ?_, hdiv⟩
        · by_contra h
          exact hnot ⟨Nat.lt_of_not_le h, hdiv⟩
        · exact Nat.le_of_lt_succ hn_lt
    rw [h1, Finset.card_sdiff]
    · 
      apply Finset.filter_subset_filter
      exact Finset.range_subset.mpr (by norm_num : 15 ≤ 86)

  
  rw [step3, step1, step2]
