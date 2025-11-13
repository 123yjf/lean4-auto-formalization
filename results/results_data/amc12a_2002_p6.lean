import Mathlib.Data.Nat.Basic
import Mathlib.Data.Set.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith




theorem amc12a_2002_p6 :
  Set.Infinite {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} := by
  
  have h_all_satisfy : ∀ m : ℕ, m > 0 → ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n := by
    intro m hm_pos
    
    use 1
    constructor
    · 
      norm_num
    · 
      simp only [mul_one]
      linarith

  
  have h_eq_pos : {m : ℕ | m > 0 ∧ ∃ n : ℕ, n > 0 ∧ m * n ≤ m + n} = {m : ℕ | m > 0} := by
    ext m
    constructor
    · 
      intro h
      exact h.1
    · 
      intro hm_pos
      constructor
      · exact hm_pos
      · exact h_all_satisfy m hm_pos

  
  rw [h_eq_pos]
  
  
  have h_inj : Function.Injective (fun n : ℕ => n + 1) := by
    intro a b h
    exact Nat.succ_injective h
  have h_range : Set.range (fun n : ℕ => n + 1) ⊆ {m : ℕ | m > 0} := by
    intro m hm
    simp only [Set.mem_range, Set.mem_setOf_eq] at hm ⊢
    obtain ⟨n, rfl⟩ := hm
    exact Nat.succ_pos n
  exact (Set.infinite_range_of_injective h_inj).mono h_range
