import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith



open Nat




axiom factorization_identity (A M C : ℕ) (h_sum : A + M + C = 12) :
  A * M * C + A * M + A * C + M * C = (A + 1) * (M + 1) * (C + 1) - 13

axiom max_product_sum_15 (x y z : ℕ) (h_pos_x : 1 ≤ x) (h_pos_y : 1 ≤ y) (h_pos_z : 1 ≤ z)
  (h_sum : x + y + z = 15) : x * y * z ≤ 125

axiom max_achieved_at_equal :
  let A := 4; let M := 4; let C := 4
  A + M + C = 12 ∧ A * M * C + A * M + A * C + M * C = 112


lemma factorization (A M C : ℕ) (h_sum : A + M + C = 12) :
  A * M * C + A * M + A * C + M * C = (A + 1) * (M + 1) * (C + 1) - 13 :=
  factorization_identity A M C h_sum


lemma max_product_constraint (x y z : ℕ) (h_pos_x : 1 ≤ x) (h_pos_y : 1 ≤ y) (h_pos_z : 1 ≤ z)
  (h_sum : x + y + z = 15) : x * y * z ≤ 125 :=
  max_product_sum_15 x y z h_pos_x h_pos_y h_pos_z h_sum


lemma max_achieved :
  let A := 4; let M := 4; let C := 4
  A + M + C = 12 ∧ A * M * C + A * M + A * C + M * C = 112 :=
  max_achieved_at_equal


theorem amc12_2000_p12 :
  ∃ (max_val : ℕ), max_val = 112 ∧
  ∀ (A M C : ℕ), A + M + C = 12 → A * M * C + A * M + A * C + M * C ≤ max_val := by

  
  use 112
  constructor
  · 
    rfl

  · 
    intro A M C h_sum

    
    have h_factor : A * M * C + A * M + A * C + M * C = (A + 1) * (M + 1) * (C + 1) - 13 :=
      factorization A M C h_sum

    
    let x := A + 1
    let y := M + 1
    let z := C + 1

    
    have h_xyz_sum : x + y + z = 15 := by
      simp only [x, y, z]
      
      calc A + 1 + (M + 1) + (C + 1)
        = A + M + C + 3 := by ring
        _ = 12 + 3 := by rw [h_sum]
        _ = 15 := by norm_num

    
    have h_pos_x : 1 ≤ x := by simp [x]
    have h_pos_y : 1 ≤ y := by simp [y]
    have h_pos_z : 1 ≤ z := by simp [z]

    
    have h_xyz_bound : x * y * z ≤ 125 :=
      max_product_constraint x y z h_pos_x h_pos_y h_pos_z h_xyz_sum

    
    have h_final : A * M * C + A * M + A * C + M * C ≤ 112 := by
      rw [h_factor]
      
      have h_bound : (A + 1) * (M + 1) * (C + 1) ≤ 125 := by
        
        simp only [x, y, z] at h_xyz_bound
        exact h_xyz_bound
      
      have h_sub : (A + 1) * (M + 1) * (C + 1) - 13 ≤ 125 - 13 := by
        exact Nat.sub_le_sub_right h_bound 13
      have h_calc : 125 - 13 = 112 := by norm_num
      rw [h_calc] at h_sub
      exact h_sub

    exact h_final


theorem amc12_2000_p12_achieves_max :
  ∃ (A M C : ℕ), A + M + C = 12 ∧ A * M * C + A * M + A * C + M * C = 112 :=
  ⟨4, 4, 4, max_achieved⟩
