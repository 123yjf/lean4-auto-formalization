import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

open ComplexConjugate




theorem amc12b_2021_p18 : ∃ (w : ℂ), ∀ (z : ℂ), z ≠ 0 →
  12 * Complex.normSq z = 2 * Complex.normSq (z + 2) + Complex.normSq (z^2 + 1) + 31 →
  z + 6 / z = w ∧ w = -2 := by
  use -2
  intro z hz_nonzero h_constraint
  constructor
  · 
    
    have h_expand : 12 * (z.re * z.re + z.im * z.im) =
      2 * ((z + 2).re * (z + 2).re + (z + 2).im * (z + 2).im) +
      ((z^2 + 1).re * (z^2 + 1).re + (z^2 + 1).im * (z^2 + 1).im) + 31 := by
      rw [← Complex.normSq_apply z, ← Complex.normSq_apply (z + 2), ← Complex.normSq_apply (z^2 + 1)]
      exact h_constraint
    
    have h_simplify : (z.re * z.re + z.im * z.im - 6) ^ 2 + 4 * (z.re + 1) ^ 2 = 0 := by
      
      have h1 : (z + 2).re = z.re + 2 := by simp [Complex.add_re]
      have h2 : (z + 2).im = z.im := by simp [Complex.add_im]
      have h3 : (z^2 + 1).re = z.re * z.re - z.im * z.im + 1 := by simp [Complex.mul_re, Complex.add_re, pow_two]
      have h4 : (z^2 + 1).im = 2 * z.re * z.im := by simp [Complex.mul_im, Complex.add_im, pow_two]; ring
      
      rw [h1, h2, h3, h4] at h_expand
      ring_nf at h_expand
      linarith [h_expand]
    
    have h_solve_system : z.re = -1 ∧ z.re * z.re + z.im * z.im = 6 := by
      
      have h_nonneg1 : 0 ≤ (z.re * z.re + z.im * z.im - 6) ^ 2 := sq_nonneg _
      have h_nonneg2 : 0 ≤ 4 * (z.re + 1) ^ 2 := by
        apply mul_nonneg
        · norm_num
        · exact sq_nonneg _
      
      have h_both_zero := add_eq_zero_iff_of_nonneg h_nonneg1 h_nonneg2
      obtain ⟨h_zero1, h_zero2⟩ := h_both_zero.mp h_simplify
      
      have h_re_eq : z.re = -1 := by
        have : (z.re + 1) ^ 2 = 0 := by linarith [h_zero2]
        exact eq_neg_of_add_eq_zero_left (pow_eq_zero this)
      
      have h_norm_eq : z.re * z.re + z.im * z.im = 6 := by
        have : (z.re * z.re + z.im * z.im - 6) ^ 2 = 0 := h_zero1
        have : z.re * z.re + z.im * z.im - 6 = 0 := pow_eq_zero this
        linarith
      exact ⟨h_re_eq, h_norm_eq⟩
    
    have h_find_z : z = -1 + Complex.I * Real.sqrt 5 ∨ z = -1 - Complex.I * Real.sqrt 5 := by
      
      obtain ⟨h_re, h_norm⟩ := h_solve_system
      
      have h_im_sq : z.im * z.im = 5 := by
        rw [h_re] at h_norm
        simp at h_norm
        linarith [h_norm]
      
      have h_im_cases : z.im = Real.sqrt 5 ∨ z.im = -Real.sqrt 5 := by
        have h_pos : 0 ≤ (5 : ℝ) := by norm_num
        have h_sq_eq : z.im ^ 2 = (Real.sqrt 5) ^ 2 := by
          rw [pow_two, pow_two]
          rw [Real.mul_self_sqrt h_pos]
          exact h_im_sq
        exact sq_eq_sq_iff_eq_or_eq_neg.mp h_sq_eq
      
      cases h_im_cases with
      | inl h_pos =>
        left
        apply Complex.ext
        · simp [Complex.add_re, Complex.mul_re, h_re]
        · simp [Complex.add_im, Complex.mul_im, h_pos]
      | inr h_neg =>
        right
        apply Complex.ext
        · simp [Complex.sub_re, Complex.mul_re, h_re]
        · simp [Complex.sub_im, Complex.mul_im, h_neg]
    
    have h_compute : z + 6 / z = -2 := by
      
      obtain ⟨h_re, h_norm⟩ := h_solve_system
      have h_norm_sq : Complex.normSq z = 6 := by
        rw [Complex.normSq_apply]
        exact h_norm
      have h_div_eq : 6 / z = conj z := by
        rw [div_eq_mul_inv, Complex.inv_def]
        simp [h_norm_sq]
        ring
      
      rw [h_div_eq]
      have h_add_conj : z + conj z = 2 * z.re := by
        apply Complex.ext
        · simp [Complex.add_re, Complex.conj_re]
          ring
        · simp [Complex.add_im, Complex.conj_im]
      rw [h_add_conj, h_re]
      norm_num
    
    exact h_compute
  · 
    rfl
