







import Mathlib.Data.Rat.Basic
import Mathlib.Tactic


theorem mathd_algebra_459 {A B C D : ℚ}
  (h1 : B + C + D = 3 * A)
  (h2 : A + C + D = 4 * B)
  (h3 : A + B + D = 2 * C)
  (h4 : 8 * A + 10 * B + 6 * C = 24) :
  D = 13 / 15 := by
  
  have hD : D = 3 * A - B - C := by
    linarith [h1]
  
  have hBcoeff : 4 * A = 5 * B := by linarith [h1, h2]
  have hB : B = (4 : ℚ) / 5 * A := by
    have h5ne : (5 : ℚ) ≠ 0 := by norm_num
    have : B = (4 * A) / 5 := (eq_div_iff_mul_eq h5ne).2 (by simpa [mul_comm] using hBcoeff.symm)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  
  have hCcoeff : 4 * A = 3 * C := by linarith [h1, h3]
  have hC : C = (4 : ℚ) / 3 * A := by
    have h3ne : (3 : ℚ) ≠ 0 := by norm_num
    have : C = (4 * A) / 3 := (eq_div_iff_mul_eq h3ne).2 (by simpa [mul_comm] using hCcoeff.symm)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  
  have hAeq : 8 * A + 10 * ((4 : ℚ) / 5 * A) + 6 * ((4 : ℚ) / 3 * A) = 24 := by
    simpa [hB, hC] using h4
  have hsum : 8 * A + 8 * A + 8 * A = 24 := by
    
    simpa [mul_assoc, mul_comm, mul_left_comm] using hAeq
  have hA : A = 1 := by linarith [hsum]
  
  have : D = 3 * A - (4 : ℚ) / 5 * A - (4 : ℚ) / 3 * A := by simpa [hB, hC] using hD
  simpa [hA] using (this.trans (by norm_num : (3 : ℚ) * 1 - (4 : ℚ) / 5 * 1 - (4 : ℚ) / 3 * 1 = 13 / 15))
