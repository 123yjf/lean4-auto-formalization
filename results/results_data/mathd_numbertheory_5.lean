import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Linarith





def IsPerfectSquare (n : ℕ) : Prop := ∃ a : ℕ, n = a^2


def IsPerfectCube (n : ℕ) : Prop := ∃ b : ℕ, n = b^3


def IsSixthPower (n : ℕ) : Prop := ∃ c : ℕ, n = c^6


theorem mathd_numbertheory_5 :
  ∃ n : ℕ, n > 10 ∧ IsPerfectSquare n ∧ IsPerfectCube n ∧
  (∀ m : ℕ, m > 10 ∧ IsPerfectSquare m ∧ IsPerfectCube m → n ≤ m) ∧
  n = 64 := by
  use 64
  constructor
  · norm_num  
  constructor
  · 
    use 8
    norm_num
  constructor
  · 
    use 4
    norm_num
  constructor
  · intro m ⟨h_gt, h_sq, h_cube⟩
    
    
    
    by_cases h : m < 64
    · 
      
      obtain ⟨a, ha⟩ := h_sq
      obtain ⟨b, hb⟩ := h_cube
      
      
      have h_sixth : IsSixthPower m := by
        
        
        
        
        
        exfalso
        
        
        
        have h_no_sixth : ∀ k : ℕ, 10 < k ∧ k < 64 → ¬IsSixthPower k := by
          intro k ⟨h_gt_k, h_lt_k⟩ h_sixth_k
          obtain ⟨c, hc⟩ := h_sixth_k
          
          have h_c_bounds : 1 < c ∧ c < 2 := by
            constructor
            · by_contra h_not
              push_neg at h_not
              interval_cases c
              · rw [hc] at h_gt_k
                norm_num at h_gt_k
              · rw [hc] at h_gt_k
                norm_num at h_gt_k
            · by_contra h_not
              push_neg at h_not
              have h_c_ge_2 : c ≥ 2 := h_not
              rw [hc] at h_lt_k
              have h_64_le : 64 ≤ c^6 := by
                have h_2_6 : (2 : ℕ)^6 = 64 := by norm_num
                rw [← h_2_6]
                exact pow_le_pow_left' h_c_ge_2 6
              exact absurd h_64_le (not_le.mpr h_lt_k)
          
          have h_c_eq_2 : c = 2 := by
            have h_c_ge_2 : c ≥ 2 := Nat.succ_le_of_lt h_c_bounds.1
            have h_c_le_1 : c ≤ 1 := Nat.le_of_succ_le_succ h_c_bounds.2
            linarith [h_c_ge_2, h_c_le_1]
          
          rw [h_c_eq_2] at h_c_bounds
          exact absurd h_c_bounds.2 (not_lt.mpr (le_refl 2))
        
        
        
        
        
        
        
        
        
        
        
        
        
        exfalso
        
        have h_not_16 : ¬IsPerfectCube 16 := by
          intro ⟨c, hc⟩
          
          have h_c_bound : c ≤ 3 := by
            by_contra h_not
            push_neg at h_not
            have h_c_ge_4 : c ≥ 4 := h_not
            have h_c3_ge_64 : c^3 ≥ 4^3 := pow_le_pow_left' h_c_ge_4 3
            rw [← hc] at h_c3_ge_64
            norm_num at h_c3_ge_64
          interval_cases c <;> norm_num at hc
        have h_not_25 : ¬IsPerfectCube 25 := by
          intro ⟨c, hc⟩
          
          have h_c_bound : c ≤ 3 := by
            by_contra h_not
            push_neg at h_not
            have h_c_ge_4 : c ≥ 4 := h_not
            have h_c3_ge_64 : c^3 ≥ 4^3 := pow_le_pow_left' h_c_ge_4 3
            rw [← hc] at h_c3_ge_64
            norm_num at h_c3_ge_64
          interval_cases c <;> norm_num at hc
        have h_not_36 : ¬IsPerfectCube 36 := by
          intro ⟨c, hc⟩
          
          have h_c_bound : c ≤ 4 := by
            by_contra h_not
            push_neg at h_not
            have h_c_ge_5 : c ≥ 5 := h_not
            have h_c3_ge_125 : c^3 ≥ 5^3 := pow_le_pow_left' h_c_ge_5 3
            rw [← hc] at h_c3_ge_125
            norm_num at h_c3_ge_125
          interval_cases c <;> norm_num at hc
        have h_not_49 : ¬IsPerfectCube 49 := by
          intro ⟨c, hc⟩
          
          have h_c_bound : c ≤ 4 := by
            by_contra h_not
            push_neg at h_not
            have h_c_ge_5 : c ≥ 5 := h_not
            have h_c3_ge_125 : c^3 ≥ 5^3 := pow_le_pow_left' h_c_ge_5 3
            rw [← hc] at h_c3_ge_125
            norm_num at h_c3_ge_125
          interval_cases c <;> norm_num at hc
        have h_not_27 : ¬IsPerfectSquare 27 := by
          intro ⟨a, ha⟩
          
          have h_a_bound : a ≤ 6 := by
            by_contra h_not
            push_neg at h_not
            have : a ≥ 7 := h_not
            have : a^2 ≥ 7^2 := pow_le_pow_left' this 2
            rw [← ha] at this
            norm_num at this
          interval_cases a <;> norm_num at ha
        
        
        
        
        
        
        
        
        have h_m_sixth : IsSixthPower m := by
          
          
          
          use 2  
          
          
          
          exfalso
          
          
          
          
          
          
          
          
          have h_impossible : False := by
            
            
            
            
            
            
            
            
            
            
            
            have h_no_both : ∀ k : ℕ, 10 < k ∧ k < 64 → ¬(IsPerfectSquare k ∧ IsPerfectCube k) := by
              intro k ⟨h_k_gt, h_k_lt⟩ ⟨h_k_sq, h_k_cube⟩
              
              by_cases h_k_16 : k = 16
              · rw [h_k_16] at h_k_cube
                exact h_not_16 h_k_cube
              · by_cases h_k_25 : k = 25
                · rw [h_k_25] at h_k_cube
                  exact h_not_25 h_k_cube
                · by_cases h_k_36 : k = 36
                  · rw [h_k_36] at h_k_cube
                    exact h_not_36 h_k_cube
                  · by_cases h_k_49 : k = 49
                    · rw [h_k_49] at h_k_cube
                      exact h_not_49 h_k_cube
                    · by_cases h_k_27 : k = 27
                      · rw [h_k_27] at h_k_sq
                        exact h_not_27 h_k_sq
                      · 
                        
                        
                        
                        exfalso
                        
                        
                        
                        
                        
                        
                        
                        
                        have h_k_sixth : IsSixthPower k := by
                          
                          
                          
                          
                          use 2  
                          
                          
                          exfalso
                          
                          
                          
                          
                          
                          
                          
                          exact h_no_sixth k ⟨h_k_gt, h_k_lt⟩ h_k_sixth
                        exact h_no_sixth k ⟨h_k_gt, h_k_lt⟩ h_k_sixth
            exact h_no_both m ⟨h_gt, h⟩ ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
          exact h_impossible
        exact h_no_sixth m ⟨h_gt, h⟩ h_m_sixth
      
      obtain ⟨c, hc⟩ := h_sixth
      
      have h_c_bounds : 1 < c ∧ c < 2 := by
        constructor
        · by_contra h_not_1
          push_neg at h_not_1
          interval_cases c
          · rw [hc] at h_gt
            norm_num at h_gt
          · rw [hc] at h_gt
            norm_num at h_gt
        · by_contra h_not_2
          push_neg at h_not_2
          have h_c_ge_2 : c ≥ 2 := h_not_2
          rw [hc] at h
          have h_64_le : 64 ≤ c^6 := by
            have h_2_6 : (2 : ℕ)^6 = 64 := by norm_num
            rw [← h_2_6]
            exact pow_le_pow_left' h_c_ge_2 6
          exact absurd h_64_le (not_le.mpr h)
      
      have h_c_eq_2 : c = 2 := by
        have h_c_ge_2 : c ≥ 2 := Nat.succ_le_of_lt h_c_bounds.1
        have h_c_le_1 : c ≤ 1 := Nat.le_of_succ_le_succ h_c_bounds.2
        linarith [h_c_ge_2, h_c_le_1]
      
      rw [h_c_eq_2] at h_c_bounds
      exact absurd h_c_bounds.2 (not_lt.mpr (le_refl 2))
    · 
      push_neg at h
      exact h
  · rfl  


lemma perfect_square_and_cube_iff_sixth_power (n : ℕ) :
  IsPerfectSquare n ∧ IsPerfectCube n ↔ IsSixthPower n := by
  constructor
  · intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    
    
    by_cases h : n = 0
    · use 0
      rw [h]
      norm_num
    · by_cases h1 : n = 1
      · use 1
        rw [h1]
        norm_num
      · 
        
        sorry
  · intro ⟨c, hc⟩
    constructor
    · use c^3
      rw [hc]
      ring
    · use c^2
      rw [hc]
      ring


lemma is_perfect_square_64 : IsPerfectSquare 64 := by
  use 8
  norm_num


lemma is_perfect_cube_64 : IsPerfectCube 64 := by
  use 4
  norm_num


lemma is_sixth_power_64 : IsSixthPower 64 := by
  use 2
  norm_num


lemma sixth_powers_enumeration :
  1^6 = 1 ∧ 2^6 = 64 ∧ 3^6 = 729 := by
  norm_num


lemma minimality_64 :
  ∀ n : ℕ, n > 10 ∧ IsSixthPower n → n ≥ 64 := by
  intro n ⟨h_gt, h_sixth⟩
  
  obtain ⟨c, hc⟩ := h_sixth
  
  have h_c_ge_2 : c ≥ 2 := by
    by_contra h_not
    push_neg at h_not
    interval_cases c
    · rw [hc] at h_gt
      norm_num at h_gt
    · rw [hc] at h_gt
      norm_num at h_gt
  
  rw [hc]
  have h_2_le_c : 2 ≤ c := h_c_ge_2
  have h_64 : (2 : ℕ)^6 = 64 := by norm_num
  rw [← h_64]
  
  exact pow_le_pow_left' h_2_le_c 6


lemma no_sixth_power_between_10_and_64 :
  ∀ n : ℕ, 10 < n ∧ n < 64 → ¬IsSixthPower n := by
  intro n ⟨h_gt, h_lt⟩ h_sixth
  
  obtain ⟨c, hc⟩ := h_sixth
  
  have h_c_bounds : 1 < c ∧ c < 2 := by
    constructor
    · by_contra h_not
      push_neg at h_not
      interval_cases c
      · rw [hc] at h_gt
        norm_num at h_gt
      · rw [hc] at h_gt
        norm_num at h_gt
    · by_contra h_not
      push_neg at h_not
      have h_c_ge_2 : c ≥ 2 := h_not
      rw [hc] at h_lt
      have h_64_le : 64 ≤ c^6 := by
        have h_2_6 : (2 : ℕ)^6 = 64 := by norm_num
        rw [← h_2_6]
        exact pow_le_pow_left' h_c_ge_2 6
      exact absurd h_64_le (not_le.mpr h_lt)
  
  have h_c_eq_2 : c = 2 := by
    have h_c_ge_2 : c ≥ 2 := Nat.succ_le_of_lt h_c_bounds.1
    have h_c_le_1 : c ≤ 1 := Nat.le_of_succ_le_succ h_c_bounds.2
    linarith [h_c_ge_2, h_c_le_1]
  
  rw [h_c_eq_2] at h_c_bounds
  exact not_lt.mpr (le_refl 2) h_c_bounds.2
