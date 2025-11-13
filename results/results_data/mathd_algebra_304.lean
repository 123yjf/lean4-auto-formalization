import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_algebra_304 : (91 : ℕ)^2 = 8281 := by
  
  have method_a : (90 + 1 : ℕ)^2 = 8281 := by
    
    
    have expansion : (90 + 1 : ℕ)^2 = 90^2 + 2 * 90 * 1 + 1^2 := by
      ring
    
    have calculation : 90^2 + 2 * 90 * 1 + 1^2 = 8281 := by
      norm_num
    rw [expansion, calculation]

  
  have method_b : (100 - 9 : ℕ)^2 = 8281 := by
    
    
    have expansion : (100 - 9 : ℕ)^2 = 100^2 - 2 * 100 * 9 + 9^2 := by
      ring
    
    have calculation : 100^2 - 2 * 100 * 9 + 9^2 = 8281 := by
      norm_num
    rw [expansion, calculation]

  
  have eq_method_a : (91 : ℕ) = 90 + 1 := by
    norm_num

  
  rw [eq_method_a]
  exact method_a
