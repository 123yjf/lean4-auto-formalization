import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace MathdAlgebra342


noncomputable def S (a d : ℝ) (n : ℕ) : ℝ := (n:ℝ)/2 * (2*a + ((n:ℝ) - 1)*d)

theorem solve_first_term
    (a d : ℝ)
    (h5  : S a d 5 = 70)
    (h10 : S a d 10 = 210) :
    a = 42/5 := by
  
  
  have h5r : (5:ℝ)/2 * (2*a + 4*d) = 70 := by
    simpa [S, show (5:ℝ) - 1 = 4 by norm_num] using h5

  
  
  have h1m : 5 * (2*a + 4*d) = 140 := by
    have h := h5r
    field_simp at h
    simpa [mul_comm, mul_left_comm, mul_assoc, show (2:ℝ) * 70 = 140 by norm_num] using h
  have h1 : 2*a + 4*d = 28 := by
    have : (2*a + 4*d) * 5 = 140 := by simpa [mul_comm] using h1m
    have : (2*a + 4*d) = 140 / 5 :=
      (eq_div_iff_mul_eq (by norm_num : (5:ℝ) ≠ 0)).2 this
    simpa [show (140:ℝ) / 5 = 28 by norm_num] using this
  
  have h10r : (10:ℝ)/2 * (2*a + 9*d) = 210 := by
    simpa [S, show (10:ℝ) - 1 = 9 by norm_num] using h10

  have h2m : 10 * (2*a + 9*d) = 420 := by
    have h := h10r
    field_simp at h
    simpa [mul_comm, mul_left_comm, mul_assoc, show (2:ℝ) * 210 = 420 by norm_num] using h
  have h2 : 2*a + 9*d = 42 := by
    have : (2*a + 9*d) * 10 = 420 := by simpa [mul_comm] using h2m
    have : (2*a + 9*d) = 420 / 10 :=
      (eq_div_iff_mul_eq (by norm_num : (10:ℝ) ≠ 0)).2 this
    simpa [show (420:ℝ) / 10 = 42 by norm_num] using this
  
  have hdlin : 5*d = 14 := by linarith [h1, h2]
  have hd : d = 14/5 := by
    have hd' : d * 5 = 14 := by simpa [mul_comm] using hdlin
    exact (eq_div_iff_mul_eq (by norm_num : (5:ℝ) ≠ 0)).2 hd'
  
  have h2a : 2*a = 84/5 := by
    have hx : 2*a = 28 - 4*d := by linarith [h1]
    have hx' : 2*a = 28 - 4*(14/5) := by simpa [hd] using hx
    simpa [show (28:ℝ) - 4*(14/5) = 84/5 by norm_num] using hx'
  have h2a' : a * 2 = 84/5 := by simpa [mul_comm] using h2a
  have a_eq : a = (84:ℝ)/5 / 2 :=
    (eq_div_iff_mul_eq (by norm_num : (2:ℝ) ≠ 0)).2 h2a'
  simpa [show (84:ℝ)/5 / 2 = 42/5 by norm_num] using a_eq
end MathdAlgebra342
