import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith





theorem amc12b_2020_p6 (n : ℕ) (hn : n ≥ 9) :
  ∃ k : ℕ, (Nat.factorial (n + 2) - Nat.factorial (n + 1)) / Nat.factorial n = k^2 := by
  
  use (n + 1)

  
  

  
  have factorial_expansion : Nat.factorial (n + 2) = (n + 2) * (n + 1) * Nat.factorial n := by
    
    
    rw [Nat.factorial_succ (n + 1)]
    rw [Nat.factorial_succ n]
    
    
    simp only [Nat.add_assoc]
    ring

  
  have factorial_expansion_succ : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
    
    exact Nat.factorial_succ n

  
  have numerator_simplification : Nat.factorial (n + 2) - Nat.factorial (n + 1) = (n + 1) * (n + 1) * Nat.factorial n := by
    
    rw [Nat.factorial_succ (n + 1)]
    rw [Nat.factorial_succ n]
    
    
    simp only [Nat.add_assoc]
    
    
    rw [← Nat.mul_assoc]
    
    have h : (n + 2) * (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n = (n + 1) * (n + 1) * Nat.factorial n := by
      
      calc (n + 2) * (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n
        = (n + 1 + 1) * (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n := by norm_num
        _ = ((n + 1) + 1) * (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n := by rfl
        _ = (n + 1) * (n + 1) * Nat.factorial n + 1 * (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n := by rw [Nat.add_mul]; ring_nf
        _ = (n + 1) * (n + 1) * Nat.factorial n + (n + 1) * Nat.factorial n - (n + 1) * Nat.factorial n := by rw [Nat.one_mul]
        _ = (n + 1) * (n + 1) * Nat.factorial n := by rw [Nat.add_sub_cancel]
    exact h

  
  have division_property : ∀ a b c : ℕ, b ≠ 0 → c ≠ 0 → a = b * c → a / b = c := by
    intros a b c hb_ne_zero hc_ne_zero h_eq
    rw [h_eq]
    exact Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hb_ne_zero)

  
  have n_factorial_nonzero : Nat.factorial n ≠ 0 := by
    exact Nat.factorial_ne_zero n

  
  rw [show (n + 1)^2 = (n + 1) * (n + 1) by ring]
  apply division_property
  · exact n_factorial_nonzero
  · norm_num
  · rw [numerator_simplification]
    ring
