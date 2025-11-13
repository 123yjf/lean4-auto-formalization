import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Order.Field.Basic



open Int Rat


lemma sum_three_fractions : (1 : ℚ) / 2 + 1 / 3 + 1 / 7 = 41 / 42 := by
  
  
  
  norm_num


theorem sum_is_integer_iff_n_eq_42 :
  (1 : ℚ) / 2 + 1 / 3 + 1 / 7 + 1 / 42 = 1 := by
  rw [sum_three_fractions]
  norm_num


theorem unique_solution_n_eq_42 (n : ℕ) (hn : 0 < n) :
  (∃ k : ℤ, (1 : ℚ) / 2 + 1 / 3 + 1 / 7 + 1 / n = k) ↔ n = 42 := by
  constructor
  · 
    intro ⟨k, hk⟩
    
    have h_sum : (1 : ℚ) / 2 + 1 / 3 + 1 / 7 = 41 / 42 := sum_three_fractions
    rw [h_sum] at hk
    
    

    
    
    
    have h_k_eq_1 : k = 1 := by
      
      have h_41_42_lt_1 : (41 : ℚ) / 42 < 1 := by norm_num
      have h_pos : (0 : ℚ) < 1 / n := by
        simp [one_div_pos, Nat.cast_pos.mpr hn]
      have h_lower : (41 : ℚ) / 42 < k := by
        rw [← hk]
        exact lt_add_of_pos_right _ h_pos
      
      have h_upper : (k : ℚ) < 2 := by
        have h_bound : (1 : ℚ) / n ≤ 1 := by
          
          have h_ge_1 : 1 ≤ n := Nat.succ_le_of_lt hn
          have h_pos_n : (0 : ℚ) < n := Nat.cast_pos.mpr hn
          
          
          have h_n_ge_1 : (1 : ℚ) ≤ n := Nat.one_le_cast.mpr h_ge_1
          
          
          rw [div_le_one h_pos_n]
          exact h_n_ge_1
        have h_eq_k : (41 : ℚ) / 42 + 1 / n = k := hk
        have h_le : (41 : ℚ) / 42 + 1 / n ≤ 41 / 42 + 1 := add_le_add_left h_bound _
        rw [h_eq_k] at h_le
        have h_lt_2 : (41 : ℚ) / 42 + 1 < 2 := by norm_num
        have : (k : ℚ) ≤ 41 / 42 + 1 := h_le
        exact lt_of_le_of_lt this h_lt_2
      
      
      
      
      
      have h_41_42_approx : (41 : ℚ) / 42 = 41 / 42 := rfl
      have h_41_42_val : (41 : ℚ) / 42 < 1 := by norm_num
      have h_k_ge_1 : 1 ≤ k := by
        
        have h_pos_41_42 : (0 : ℚ) < 41 / 42 := by norm_num
        have h_k_gt_41_42 : (41 : ℚ) / 42 < k := h_lower
        have h_k_pos : (0 : ℚ) < k := lt_trans h_pos_41_42 h_k_gt_41_42
        
        by_contra h_not
        push_neg at h_not
        have : k ≤ 0 := Int.le_of_lt_add_one h_not
        have : (k : ℚ) ≤ 0 := Int.cast_le.mpr this
        exact not_le.mpr h_k_pos this
      have h_k_le_1 : k ≤ 1 := by
        
        have h_k_lt_2 : (k : ℚ) < 2 := h_upper
        by_contra h_not
        push_neg at h_not
        have : 2 ≤ k := Int.add_one_le_of_lt h_not
        have : (2 : ℚ) ≤ k := Int.cast_le.mpr this
        exact not_le.mpr h_k_lt_2 this
      exact le_antisymm h_k_le_1 h_k_ge_1

    
    subst h_k_eq_1
    have h_eq : (1 : ℚ) / n = 1 / 42 := by
      have h_eq_1 : (41 : ℚ) / 42 + 1 / n = 1 := hk
      have h_sub : (1 : ℚ) / n = 1 - 41 / 42 := by
        have h_add : (1 : ℚ) / n + 41 / 42 = 1 := by rw [add_comm]; exact h_eq_1
        exact eq_sub_iff_add_eq.mpr h_add
      rw [h_sub]
      norm_num

    
    have hn_pos : (0 : ℚ) < n := Nat.cast_pos.mpr hn
    have h42_pos : (0 : ℚ) < 42 := by norm_num
    have h_ne_zero_n : (n : ℚ) ≠ 0 := ne_of_gt hn_pos
    have h_ne_zero_42 : (42 : ℚ) ≠ 0 := by norm_num
    have : (n : ℚ) = 42 := by
      have : 1 / (n : ℚ) = 1 / 42 := h_eq
      rw [div_eq_div_iff h_ne_zero_n h_ne_zero_42] at this
      simp at this
      exact this.symm
    exact Nat.cast_injective this
  · 
    intro hn42
    subst hn42
    use 1
    exact sum_is_integer_iff_n_eq_42
