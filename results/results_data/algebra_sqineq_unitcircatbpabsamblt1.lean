import Mathlib

open Real


theorem algebra_sqineq_unitcircatbpabsamblt1
    {a b : ℝ} (h : a^2 + b^2 = 1) : a*b + |a - b| ≤ 1 := by
  
  have hsq : (a - b)^2 = 1 - 2*(a*b) := by
    have hx : (a - b)^2 = a^2 + b^2 - 2*(a*b) := by ring
    simpa [hx, h]
  
  have h0 : 0 ≤ 1 - 2*(a*b) := by
    simpa [hsq] using sq_nonneg (a - b)
  
  have hAbs : |a - b| = Real.sqrt (1 - 2*(a*b)) := by
    have : Real.sqrt ((a - b)^2) = |a - b| := by
      simpa using Real.sqrt_sq_eq_abs (a - b)
    simpa [hsq] using this.symm
  
  have hab_le_half : a*b ≤ (1/2 : ℝ) := by
    have h2ab_le_one : 2*(a*b) ≤ 1 := (sub_nonneg.mp h0)
    have hnonneg_half : 0 ≤ (1/2 : ℝ) := by norm_num
    have := mul_le_mul_of_nonneg_left h2ab_le_one hnonneg_half
    
    simpa using this
  
  have hab_le_one : a*b ≤ (1 : ℝ) := le_trans hab_le_half (by norm_num)
  have h1_nonneg : 0 ≤ 1 - a*b := sub_nonneg.mpr hab_le_one
  
  have hSqrt_le : Real.sqrt (1 - 2*(a*b)) ≤ 1 - a*b := by
    
    have hdiff_nonneg : 0 ≤ (1 - a*b)^2 - (1 - 2*(a*b)) := by
      have : (1 - a*b)^2 - (1 - 2*(a*b)) = (a*b)^2 := by ring
      simpa [this] using (sq_nonneg (a*b))
    have hpoly : 1 - 2*(a*b) ≤ (1 - a*b)^2 := (sub_nonneg.mp hdiff_nonneg)
    
    exact (Real.sqrt_le_iff).mpr ⟨h1_nonneg, by simpa [pow_two] using hpoly⟩
  
  
  have : a*b + |a - b| ≤ a*b + (1 - a*b) := by
    simpa [hAbs] using add_le_add_left hSqrt_le (a*b)
  simpa using this
