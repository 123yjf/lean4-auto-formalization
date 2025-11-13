import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real


 theorem mathd_algebra_293 (x : ℝ) (hx : 0 ≤ x) :
   sqrt (60*x) * sqrt (12*x) * sqrt (63*x) = 36*x*sqrt (35*x) := by
  
  have h60 : 0 ≤ 60 * x := by exact mul_nonneg (by norm_num) hx
  have h12 : 0 ≤ 12 * x := by exact mul_nonneg (by norm_num) hx
  have h63 : 0 ≤ 63 * x := by exact mul_nonneg (by norm_num) hx
  have h12c : sqrt (60*x) * sqrt (12*x) = sqrt ((60*x) * (12*x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.sqrt_mul h60 h12).symm
  
  have h6012_nonneg : 0 ≤ (60*x) * (12*x) := mul_nonneg h60 h12
  have h3 : sqrt ((60*x) * (12*x)) * sqrt (63*x)
      = sqrt (((60*x) * (12*x)) * (63*x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.sqrt_mul h6012_nonneg h63).symm
  have hcomb : sqrt (60*x) * sqrt (12*x) * sqrt (63*x)
      = sqrt (((60*x) * (12*x)) * (63*x)) := by
    simpa [h12c, mul_comm, mul_left_comm, mul_assoc] using h3
  
  have hins : ((60*x) * (12*x)) * (63*x) = (60*12*63 : ℝ) * x^3 := by
    simp [pow_three, mul_comm, mul_left_comm, mul_assoc]
  
  have hnum : (60*12*63 : ℝ) = (36:ℝ)^2 * 35 := by norm_num
  
  have hmove : sqrt (((60*12*63 : ℝ)) * x^3)
      = sqrt ((36:ℝ)^2 * (35 * x^3)) := by
    have := congrArg (fun t : ℝ => sqrt (t * x^3)) hnum
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  
  have hpos36 : 0 ≤ (36:ℝ)^2 := by have : (0:ℝ) ≤ 36 := by norm_num; exact sq_nonneg _
  have hx3 : 0 ≤ x^3 := by simpa using pow_nonneg hx (3:ℕ)
  have hsplit1 : sqrt ((36:ℝ)^2 * (35 * x^3))
      = sqrt ((36:ℝ)^2) * sqrt (35 * x^3) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.sqrt_mul (by positivity) (by nlinarith [hx])).symm
  
  have hs36 : sqrt ((36:ℝ)^2) = 36 := by
    simpa [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 36)] using
      Real.sqrt_sq_eq_abs (36:ℝ)
  
  have hx2 : 0 ≤ x^2 := by have : 0 ≤ x^2 := sq_nonneg x; simpa [pow_two] using this
  have hx_mul : sqrt (x^2 * x) = sqrt (x^2) * sqrt x := by
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      (Real.sqrt_mul hx2 hx).symm
  have hsx2 : sqrt (x^2) = x := by
    have := Real.sqrt_sq_eq_abs x
    simpa [abs_of_nonneg hx, pow_two] using this
  
  have h35x3 : sqrt (35 * x^3) = sqrt 35 * sqrt (x^3) := by
    have h35 : 0 ≤ (35:ℝ) := by norm_num
    have hx3' : 0 ≤ x^3 := by simpa using pow_nonneg hx (3:ℕ)
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.sqrt_mul h35 hx3').symm
  
  calc
    sqrt (60*x) * sqrt (12*x) * sqrt (63*x)
        = sqrt (((60*x) * (12*x)) * (63*x)) := hcomb
    _ = sqrt ((60*12*63 : ℝ) * x^3) := by simpa [hins]
    _ = sqrt ((36:ℝ)^2 * (35 * x^3)) := hmove
    _ = sqrt ((36:ℝ)^2) * sqrt (35 * x^3) := hsplit1
    _ = 36 * (sqrt 35 * sqrt (x^3)) := by simpa [hs36]
    _ = 36 * (sqrt 35 * (sqrt (x^2) * sqrt x)) := by
          simpa [pow_three, mul_comm, mul_left_comm, mul_assoc] using congrArg (fun t => 36 * (sqrt 35 * t)) (by
            simpa [pow_three, mul_comm, mul_left_comm, mul_assoc] using congrArg (fun t => t) h35x3)
    _ = 36 * (sqrt 35 * (x * sqrt x)) := by simpa [hsx2, hx_mul]
    _ = 36 * x * sqrt (35 * x) := by
          have : sqrt 35 * sqrt x = sqrt (35 * x) := by
            have h35 : 0 ≤ (35:ℝ) := by norm_num
            simpa [mul_comm] using (Real.sqrt_mul h35 hx).symm
          simpa [mul_comm, mul_left_comm, mul_assoc, this]
