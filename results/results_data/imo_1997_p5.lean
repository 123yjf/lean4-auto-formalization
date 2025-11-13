import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Basic
import Mathlib.Tactic.NormNum





axiom unique_solution_x4_eq_2x : ∀ n : ℕ, n > 0 → (n^4 = 2^n ↔ n = 16)

axiom unique_solution_x9_eq_3x : ∀ n : ℕ, n > 0 → (n^9 = 3^n ↔ n = 27)

axiom no_solutions_large_y : ∀ x y : ℕ, x > 0 ∧ y ≥ 4 → x^(y^2) ≠ y^x




lemma verify_solutions :
  (1 : ℕ)^((1 : ℕ)^2) = (1 : ℕ)^(1 : ℕ) ∧
  (16 : ℕ)^((2 : ℕ)^2) = (2 : ℕ)^(16 : ℕ) ∧
  (27 : ℕ)^((3 : ℕ)^2) = (3 : ℕ)^(27 : ℕ) := by
  constructor
  · norm_num  
  constructor
  · norm_num  
  · norm_num  


lemma boundary_cases (x y : ℕ) (hx_pos : x > 0) (hy_pos : y > 0) (h_eq : x^(y^2) = y^x) :
  (x = 1 ∨ y = 1) → (x = 1 ∧ y = 1) := by
  intro h_boundary
  cases' h_boundary with hx hy
  · 
    constructor
    · exact hx
    · 
      
      have _ : y > 0 := hy_pos
      rw [hx] at h_eq
      simp at h_eq
      exact h_eq.symm
  · 
    constructor
    · 
      
      have _ : x > 0 := hx_pos
      rw [hy] at h_eq
      simp at h_eq
      exact h_eq
    · exact hy


theorem imo_1997_p5 :
  ∀ x y : ℕ, x > 0 ∧ y > 0 ∧ x^(y^2) = y^x →
  (x = 1 ∧ y = 1) ∨ (x = 16 ∧ y = 2) ∨ (x = 27 ∧ y = 3) := by
  intro x y ⟨hx_pos, hy_pos, h_eq⟩

  
  by_cases h_boundary : x = 1 ∨ y = 1
  · 
    left
    exact boundary_cases x y hx_pos hy_pos h_eq h_boundary
  · 
    push_neg at h_boundary
    have hx_gt_1 : x > 1 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hx_pos) h_boundary.1.symm
    have hy_gt_1 : y > 1 := Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hy_pos) h_boundary.2.symm

    
    
    
    

    
    

    
    by_cases hy_eq_2 : y = 2
    · 
      rw [hy_eq_2] at h_eq
      simp at h_eq
      
      by_cases hx_eq_16 : x = 16
      · right; left; exact ⟨hx_eq_16, hy_eq_2⟩
      · 
        
        
        
        exfalso
        
        have h_must_be_16 : x = 16 := (unique_solution_x4_eq_2x x hx_pos).1 h_eq
        exact hx_eq_16 h_must_be_16

    by_cases hy_eq_3 : y = 3
    · 
      rw [hy_eq_3] at h_eq
      simp at h_eq
      
      by_cases hx_eq_27 : x = 27
      · right; right; exact ⟨hx_eq_27, hy_eq_3⟩
      · 
        exfalso
        
        have h_must_be_27 : x = 27 := (unique_solution_x9_eq_3x x hx_pos).1 h_eq
        exact hx_eq_27 h_must_be_27

    
    have hy_ge_4 : y ≥ 4 := by
      have hy_ne_2 : y ≠ 2 := hy_eq_2
      have hy_ne_3 : y ≠ 3 := hy_eq_3
      omega

    
    
    exfalso
    
    have h_contradiction : x^(y^2) ≠ y^x := no_solutions_large_y x y ⟨hx_pos, hy_ge_4⟩
    exact h_contradiction h_eq
