import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic


theorem imo_1965_p2 [DecidableEq (Fin 3)] (A : Matrix (Fin 3) (Fin 3) ℝ)
  (h_diag_pos : ∀ i, 0 < A i i)
  (h_off_diag_neg : ∀ i j, i ≠ j → A i j < 0)
  (h_row_sum_pos : ∀ i, 0 < ∑ j, A i j) :
  ∀ x : Fin 3 → ℝ, (∀ i, ∑ j, A i j * x j = 0) → (∀ i, x i = 0) := by

  
  intro x hx

  
  have h_strict_diag_dom : ∀ i, A i i > ∑ j ∈ Finset.univ.erase i, |A i j| := by
    intro i
    
    have h_pos := h_row_sum_pos i
    rw [← Finset.add_sum_erase Finset.univ (fun j => A i j) (Finset.mem_univ i)] at h_pos
    
    have h_abs : ∑ j ∈ Finset.univ.erase i, |A i j| = ∑ j ∈ Finset.univ.erase i, -(A i j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [abs_of_neg (h_off_diag_neg i j (Finset.ne_of_mem_erase hj).symm)]
    rw [h_abs]
    have h_neg : ∑ j ∈ Finset.univ.erase i, -(A i j) = -(∑ j ∈ Finset.univ.erase i, A i j) := by
      rw [Finset.sum_neg_distrib]
    rw [h_neg]
    
    linarith

  
  have h_nonsingular : A.det ≠ 0 := by
    apply det_ne_zero_of_sum_row_lt_diag
    intro k
    
    have h_lt := h_strict_diag_dom k
    rw [gt_iff_lt] at h_lt
    
    have h_norm_eq : ∑ j ∈ Finset.univ.erase k, ‖A k j‖ = ∑ j ∈ Finset.univ.erase k, |A k j| := by
      apply Finset.sum_congr rfl
      intro j hj
      rfl
    
    have h_diag_norm : ‖A k k‖ = A k k := Real.norm_of_nonneg (le_of_lt (h_diag_pos k))
    rw [h_norm_eq, h_diag_norm]
    exact h_lt

  
  have h_trivial : x = 0 := by
    
    have h_mulVec : Matrix.mulVec A x = 0 := by
      funext i
      simp only [Matrix.mulVec, Matrix.dotProduct, Pi.zero_apply]
      exact hx i
    
    exact Matrix.eq_zero_of_mulVec_eq_zero h_nonsingular h_mulVec

  
  intro i
  rw [h_trivial]
  simp
