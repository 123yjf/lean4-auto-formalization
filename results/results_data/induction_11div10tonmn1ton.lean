import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


theorem induction_11div10tonmn1ton (n : ℕ) : 11 ∣ (10^n - (-1 : ℤ)^n) := by
  
  
  have h1 : (10 : ℤ) ≡ (-1 : ℤ) [ZMOD 11] := by
    rw [Int.ModEq]
    norm_num

  
  have h2 : (10 : ℤ)^n ≡ (-1 : ℤ)^n [ZMOD 11] := by
    exact h1.pow n

  
  have h3 : (10 : ℤ)^n - (-1 : ℤ)^n ≡ 0 [ZMOD 11] := by
    rw [Int.modEq_iff_dvd] at h2
    rw [Int.modEq_zero_iff_dvd]
    rw [← Int.dvd_neg]
    convert h2 using 1
    ring

  
  exact Int.modEq_zero_iff_dvd.mp h3
