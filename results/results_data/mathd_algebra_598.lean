import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith


theorem mathd_algebra_598 :
  ∃ (a b c d : ℝ),
    Real.rpow 4 a = 5 ∧
    Real.rpow 5 b = 6 ∧
    Real.rpow 6 c = 7 ∧
    Real.rpow 7 d = 8 ∧
    a * b * c * d = 3/2 := by

  
  let a := Real.log 5 / Real.log 4
  let b := Real.log 6 / Real.log 5
  let c := Real.log 7 / Real.log 6
  let d := Real.log 8 / Real.log 7

  use a, b, c, d

  constructor
  
  · have h_4_pos : (0 : ℝ) < 4 := by norm_num
    have h_4_ne_one : (4 : ℝ) ≠ 1 := by norm_num
    have h_5_pos : (0 : ℝ) < 5 := by norm_num
    have h_a_def : a = Real.log 5 / Real.log 4 := rfl
    have h_exp : Real.rpow 4 a = 5 := by
      
      unfold a
      have h4_pos : (0 : ℝ) < 4 := by norm_num
      have h5_pos : (0 : ℝ) < 5 := by norm_num
      rw [Real.rpow_eq_pow]
      rw [← Real.mul_log_eq_log_iff h4_pos h5_pos]
      have h_log4_ne_zero : Real.log 4 ≠ 0 := by
        rw [Real.log_ne_zero]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      field_simp [h_log4_ne_zero]
    exact h_exp

  constructor
  
  · have h_5_pos : (0 : ℝ) < 5 := by norm_num
    have h_5_ne_one : (5 : ℝ) ≠ 1 := by norm_num
    have h_6_pos : (0 : ℝ) < 6 := by norm_num
    have h_b_def : b = Real.log 6 / Real.log 5 := rfl
    have h_exp : Real.rpow 5 b = 6 := by
      
      unfold b
      have h5_pos : (0 : ℝ) < 5 := by norm_num
      have h6_pos : (0 : ℝ) < 6 := by norm_num
      rw [Real.rpow_eq_pow]
      rw [← Real.mul_log_eq_log_iff h5_pos h6_pos]
      have h_log5_ne_zero : Real.log 5 ≠ 0 := by
        rw [Real.log_ne_zero]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      field_simp [h_log5_ne_zero]
    exact h_exp

  constructor
  
  · have h_6_pos : (0 : ℝ) < 6 := by norm_num
    have h_6_ne_one : (6 : ℝ) ≠ 1 := by norm_num
    have h_7_pos : (0 : ℝ) < 7 := by norm_num
    have h_c_def : c = Real.log 7 / Real.log 6 := rfl
    have h_exp : Real.rpow 6 c = 7 := by
      
      unfold c
      have h6_pos : (0 : ℝ) < 6 := by norm_num
      have h7_pos : (0 : ℝ) < 7 := by norm_num
      rw [Real.rpow_eq_pow]
      rw [← Real.mul_log_eq_log_iff h6_pos h7_pos]
      have h_log6_ne_zero : Real.log 6 ≠ 0 := by
        rw [Real.log_ne_zero]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      field_simp [h_log6_ne_zero]
    exact h_exp

  constructor
  
  · have h_7_pos : (0 : ℝ) < 7 := by norm_num
    have h_7_ne_one : (7 : ℝ) ≠ 1 := by norm_num
    have h_8_pos : (0 : ℝ) < 8 := by norm_num
    have h_d_def : d = Real.log 8 / Real.log 7 := rfl
    have h_exp : Real.rpow 7 d = 8 := by
      
      unfold d
      have h7_pos : (0 : ℝ) < 7 := by norm_num
      have h8_pos : (0 : ℝ) < 8 := by norm_num
      rw [Real.rpow_eq_pow]
      rw [← Real.mul_log_eq_log_iff h7_pos h8_pos]
      have h_log7_ne_zero : Real.log 7 ≠ 0 := by
        rw [Real.log_ne_zero]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      field_simp [h_log7_ne_zero]
    exact h_exp

  
  · have h_product : a * b * c * d = 3/2 := by
      
      
      
      unfold a b c d
      
      calc (Real.log 5 / Real.log 4) * (Real.log 6 / Real.log 5) * (Real.log 7 / Real.log 6) * (Real.log 8 / Real.log 7)
        = Real.log 8 / Real.log 4 := by field_simp; ring
        _ = 3/2 := by
          
          have h_log_8 : Real.log 8 = Real.log (2^3) := by norm_cast
          have h_log_4 : Real.log 4 = Real.log (2^2) := by norm_cast
          rw [h_log_8, h_log_4]
          rw [Real.log_pow, Real.log_pow]
          simp only [Nat.cast_ofNat]
          have h_log2_ne_zero : Real.log 2 ≠ 0 := by
            rw [Real.log_ne_zero]
            constructor
            · norm_num
            constructor
            · norm_num
            · norm_num
          field_simp [h_log2_ne_zero]
          ring
    exact h_product
