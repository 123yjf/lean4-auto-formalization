import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic


theorem factorial_lt_pow_pred (n : ℕ) (h : n ≥ 3) : n.factorial < n ^ (n - 1) := by
  
  induction n, h using Nat.le_induction with
  | base =>
    
    norm_num
  | succ k hk ih =>
    
    rw [Nat.factorial_succ]
    
    have h1 : (k + 1) * k.factorial < (k + 1) * k ^ (k - 1) := by
      exact Nat.mul_lt_mul_of_pos_left ih (Nat.succ_pos k)
    have h2 : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := by
      exact Nat.pow_le_pow_left k.le_succ (k - 1)
    have h3 : (k + 1) * (k + 1) ^ (k - 1) = (k + 1) ^ k := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    calc (k + 1) * k.factorial
      < (k + 1) * k ^ (k - 1) := h1
      _ ≤ (k + 1) * (k + 1) ^ (k - 1) := Nat.mul_le_mul_left _ h2
      _ = (k + 1) ^ k := h3
