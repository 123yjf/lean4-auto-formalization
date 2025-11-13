import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring




theorem mathd_numbertheory_247 : ∃! n : ℕ, n < 11 ∧ (3 * n : ZMod 11) = 2 := by

  
  have step1_inverse : (3 * 4 : ZMod 11) = 1 := by
    rfl

  
  have step2_range : 8 < 11 := by
    norm_num

  
  have step3_verify : (3 * 8 : ZMod 11) = 2 := by
    rfl

  
  use 8
  constructor
  · exact ⟨step2_range, step3_verify⟩
  · intros n h
    cases h with
    | intro hn_range hn_eq =>
      
      have h1 : (4 * (3 * n) : ZMod 11) = (4 * 2 : ZMod 11) := by
        rw [hn_eq]
      have h2 : (4 * (3 * n) : ZMod 11) = ((4 * 3) * n : ZMod 11) := by
        ring
      have h3 : ((4 * 3) * n : ZMod 11) = (1 * n : ZMod 11) := by
        have : (4 * 3 : ZMod 11) = 1 := step1_inverse
        rw [this]
      have h4 : (1 * n : ZMod 11) = (n : ZMod 11) := by
        ring
      have h5 : (4 * 2 : ZMod 11) = 8 := by
        rfl
      rw [h2, h3, h4, h5] at h1
      
      
      have h6 : n = 8 := by
        
        have h_n_mod : n % 11 = n := Nat.mod_eq_of_lt hn_range
        have h_8_mod : 8 % 11 = 8 := by norm_num
        
        have h_val_eq : ZMod.val (n : ZMod 11) = ZMod.val (8 : ZMod 11) := by
          exact congr_arg ZMod.val h1
        
        have h_8_val : ZMod.val (8 : ZMod 11) = 8 := by
          rfl
        rw [h_8_val] at h_val_eq
        
        have h_n_val : ZMod.val (n : ZMod 11) = n := by
          simp [ZMod.val_natCast, Nat.mod_eq_of_lt hn_range]
        rw [h_n_val] at h_val_eq
        exact h_val_eq
      exact h6


theorem direct_verification : (3 * 8 : ZMod 11) = 2 := by
  
  rfl


theorem computational_proof : ∃! n : ℕ, n < 11 ∧ (3 * n : ZMod 11) = 2 := by
  
  use 8
  constructor
  · constructor
    · norm_num  
    · decide    
  · intro n h
    
    have hn_range : n < 11 := h.1
    have hn_eq : (3 * n : ZMod 11) = 2 := h.2
    
    
    
    have h_inv : (3 * 4 : ZMod 11) = 1 := by rfl
    have h_unique : (n : ZMod 11) = (8 : ZMod 11) := by
      
      have h1 : (4 * (3 * n) : ZMod 11) = (4 * 2 : ZMod 11) := by
        rw [hn_eq]
      have h2 : (4 * (3 * n) : ZMod 11) = ((4 * 3) * n : ZMod 11) := by ring
      have h3 : ((4 * 3) * n : ZMod 11) = (1 * n : ZMod 11) := by
        rw [← h_inv]
        ring
      have h4 : (1 * n : ZMod 11) = (n : ZMod 11) := by ring
      have h5 : (4 * 2 : ZMod 11) = 8 := by rfl
      rw [h2, h3, h4, h5] at h1
      exact h1
    
    have h_val_eq : ZMod.val (n : ZMod 11) = ZMod.val (8 : ZMod 11) := by
      exact congr_arg ZMod.val h_unique
    have h_8_val : ZMod.val (8 : ZMod 11) = 8 := by rfl
    rw [h_8_val] at h_val_eq
    have h_n_val : ZMod.val (n : ZMod 11) = n := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hn_range]
    rw [h_n_val] at h_val_eq
    exact h_val_eq
