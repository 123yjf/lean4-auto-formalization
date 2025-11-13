





import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real


lemma x_eq_neg4_of_third_quadrant_dist
    (x y : ℝ) (hxneg : x < 0) (hy : y = -6)
    (hdist : (x - 8)^2 + (y - 3)^2 = 225) : x = -4 := by
  
  have h' : (x - 8)^2 + 81 = 225 := by simpa [hy] using hdist
  
  have hx_sq : (x - 8)^2 = 144 := by linarith
  
  have hx_cases : x - 8 = 12 ∨ x - 8 = -12 := by
    have hx_sq' : (x - 8)^2 = (12 : ℝ)^2 := by simpa [pow_two] using hx_sq
    exact (sq_eq_sq_iff_eq_or_eq_neg).1 hx_sq'
  have hx20_or : x = 20 ∨ x = -4 := by
    rcases hx_cases with h1 | h2
    · left;  linarith
    · right; linarith
  
  have hne20 : x ≠ 20 := by
    intro hx20
    have : (20 : ℝ) < 0 := by simpa [hx20] using hxneg
    linarith
  rcases hx20_or with hx20 | hxneg4
  · exact (hne20 hx20).elim
  · exact hxneg4


lemma distance_sq_is_52
    (x y : ℝ) (hxneg : x < 0) (hy : y = -6)
    (hdist : (x - 8)^2 + (y - 3)^2 = 225) : x^2 + y^2 = 52 := by
  have hx : x = -4 := x_eq_neg4_of_third_quadrant_dist x y hxneg hy hdist
  have hcalc : (-4 : ℝ)^2 + (-6 : ℝ)^2 = 52 := by norm_num
  simpa [hx, hy] using hcalc


theorem mathd_algebra_288
    {x y : ℝ} (hx : x < 0) (hyneg : y < 0) (hy : y = -6)
    (hdist15 : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15) :
    ∃ n : ℕ, Real.sqrt (x^2 + y^2) = Real.sqrt (n : ℝ) ∧ n = 52 := by
  
  have hx2 : 0 ≤ (x - 8)^2 := by exact sq_nonneg (x - 8)
  have hy2 : 0 ≤ (y - 3)^2 := by exact sq_nonneg (y - 3)
  have hnonneg : 0 ≤ (x - 8)^2 + (y - 3)^2 := by nlinarith
  have hsq : (x - 8)^2 + (y - 3)^2 = (15 : ℝ)^2 := by
    have h := congrArg (fun t : ℝ => t^2) hdist15
    simpa [pow_two, Real.sqrt_mul_self, abs_of_nonneg hnonneg, mul_comm, mul_left_comm, mul_assoc] using h
  have h225 : (x - 8)^2 + (y - 3)^2 = 225 := by
    simpa [show (15 : ℝ)^2 = (225 : ℝ) by norm_num] using hsq
  
  have hsum : x^2 + y^2 = 52 := distance_sq_is_52 x y hx hy h225
  refine ⟨52, ?_, rfl⟩
  simpa [hsum]



theorem mathd_algebra_288_n_value
    {x y : ℝ} (hx : x < 0) (hyneg : y < 0) (hy : y = -6)
    (hdist15 : Real.sqrt ((x - 8)^2 + (y - 3)^2) = 15) :
    ∃ n : ℕ, Real.sqrt (x^2 + y^2) = Real.sqrt (n : ℝ) ∧ n = 52 := by
  
  have hx2 : 0 ≤ (x - 8)^2 := by exact sq_nonneg (x - 8)
  have hy2 : 0 ≤ (y - 3)^2 := by exact sq_nonneg (y - 3)
  have hnonneg : 0 ≤ (x - 8)^2 + (y - 3)^2 := by nlinarith
  have hsq : (x - 8)^2 + (y - 3)^2 = (15 : ℝ)^2 := by
    have h := congrArg (fun t : ℝ => t^2) hdist15
    simpa [pow_two, Real.sqrt_mul_self, abs_of_nonneg hnonneg, mul_comm, mul_left_comm, mul_assoc] using h
  have h225 : (x - 8)^2 + (y - 3)^2 = 225 := by
    simpa [show (15 : ℝ)^2 = (225 : ℝ) by norm_num] using hsq
  
  have hsum : x^2 + y^2 = 52 := distance_sq_is_52 x y hx hy h225
  refine ⟨52, ?_, rfl⟩
  simpa [hsum]
