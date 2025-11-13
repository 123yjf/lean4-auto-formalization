import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_320 : ∃! n : ℕ, n < 101 ∧ (123456 : ℤ) ≡ (n : ℤ) [ZMOD 101] := by
  
  use 34
  constructor
  · 
    constructor
    · 
      norm_num
    · 
      
      have h1 : (100 : ℤ) ≡ -1 [ZMOD 101] := by
        
        rw [Int.ModEq]
        norm_num

      
      have h2 : (123456 : ℤ) = 1 * 10^5 + 2 * 10^4 + 3 * 10^3 + 4 * 10^2 + 5 * 10^1 + 6 * 10^0 := by
        norm_num

      
      have h3_0 : (10^0 : ℤ) ≡ 1 [ZMOD 101] := by
        simp [pow_zero]
      have h3_1 : (10^1 : ℤ) ≡ 10 [ZMOD 101] := by
        simp [pow_one]
      have h3_2 : (10^2 : ℤ) ≡ -1 [ZMOD 101] := by
        
        show (10 : ℤ) ^ 2 ≡ -1 [ZMOD 101]
        rw [Int.ModEq]
        norm_num
      have h3_3 : (10^3 : ℤ) ≡ -10 [ZMOD 101] := by
        
        show (10 : ℤ) ^ 3 ≡ -10 [ZMOD 101]
        rw [Int.ModEq]
        norm_num
      have h3_4 : (10^4 : ℤ) ≡ 1 [ZMOD 101] := by
        
        show (10 : ℤ) ^ 4 ≡ 1 [ZMOD 101]
        rw [Int.ModEq]
        norm_num
      have h3_5 : (10^5 : ℤ) ≡ 10 [ZMOD 101] := by
        
        show (10 : ℤ) ^ 5 ≡ 10 [ZMOD 101]
        rw [Int.ModEq]
        norm_num

      
      have h4 : (123456 : ℤ) ≡ 1 * 10 + 2 * 1 + 3 * (-10) + 4 * (-1) + 5 * 10 + 6 * 1 [ZMOD 101] := by
        
        rw [h2]
        
        have : 1 * 10^5 + 2 * 10^4 + 3 * 10^3 + 4 * 10^2 + 5 * 10^1 + 6 * 10^0 ≡
               1 * 10 + 2 * 1 + 3 * (-10) + 4 * (-1) + 5 * 10 + 6 * 1 [ZMOD 101] := by
          
          apply Int.ModEq.add
          · apply Int.ModEq.add
            · apply Int.ModEq.add
              · apply Int.ModEq.add
                · apply Int.ModEq.add
                  · exact Int.ModEq.mul_left 1 h3_5
                  · exact Int.ModEq.mul_left 2 h3_4
                · exact Int.ModEq.mul_left 3 h3_3
              · exact Int.ModEq.mul_left 4 h3_2
            · exact Int.ModEq.mul_left 5 h3_1
          · exact Int.ModEq.mul_left 6 h3_0
        exact this

      
      have h5 : (1 * 10 + 2 * 1 + 3 * (-10) + 4 * (-1) + 5 * 10 + 6 * 1 : ℤ) = 34 := by
        norm_num

      
      calc (123456 : ℤ) ≡ 1 * 10 + 2 * 1 + 3 * (-10) + 4 * (-1) + 5 * 10 + 6 * 1 [ZMOD 101] := h4
        _ = 34 := h5
        _ ≡ (34 : ℤ) [ZMOD 101] := Int.ModEq.refl _

  · 
    intro m hm
    
    have hm_lt : m < 101 := hm.1
    have hm_eq : (123456 : ℤ) ≡ (m : ℤ) [ZMOD 101] := hm.2
    
    have h_34_eq : (123456 : ℤ) ≡ (34 : ℤ) [ZMOD 101] := by
      rw [Int.ModEq]
      norm_num
    
    have h_34_m : (34 : ℤ) ≡ (m : ℤ) [ZMOD 101] := by
      exact Int.ModEq.trans h_34_eq.symm hm_eq
    
    rw [Int.ModEq] at h_34_m
    have h_34_mod : (34 : ℤ) % 101 = 34 := by norm_num
    have h_m_mod : (m : ℤ) % 101 = m := by
      apply Int.emod_eq_of_lt
      · exact Int.ofNat_nonneg m
      · exact Int.ofNat_lt.mpr hm_lt
    rw [h_34_mod, h_m_mod] at h_34_m
    exact Nat.cast_injective (R := ℤ) h_34_m.symm
