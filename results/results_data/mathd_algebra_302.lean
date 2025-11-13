import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum



theorem mathd_algebra_302 : (Complex.I / 2) ^ 2 = -1 / 4 := by
  
  have step1 : (Complex.I / 2) ^ 2 = Complex.I ^ 2 / 2 ^ 2 := by
    rw [div_pow]

  
  have step2 : Complex.I ^ 2 = -1 := by
    exact Complex.I_sq

  
  have step3 : (2 : ℂ) ^ 2 = 4 := by
    norm_num

  
  rw [step1, step2, step3]
