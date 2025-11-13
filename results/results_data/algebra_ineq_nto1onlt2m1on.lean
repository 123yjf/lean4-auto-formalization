import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring





theorem algebra_ineq_nto1onlt2m1on (n : ℕ) (hn : 0 < n) :
  (n : ℝ) ^ ((1 : ℝ) / n) ≤ 2 - (1 : ℝ) / n := by
  
  
  
  
  

  
  have h_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h_ne_zero : (n : ℝ) ≠ 0 := ne_of_gt h_pos

  
  have weight1 : (n - 1 : ℝ) / n + (1 : ℝ) / n = 1 := by
    field_simp [h_ne_zero]

  
  have h_one_le : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (ne_of_gt hn)
  have hw1_nonneg : (0 : ℝ) ≤ (n - 1 : ℝ) / n := by
    apply div_nonneg
    · rw [← Nat.cast_one, ← Nat.cast_sub h_one_le]
      exact Nat.cast_nonneg _
    · exact le_of_lt h_pos

  have hw2_nonneg : (0 : ℝ) ≤ (1 : ℝ) / n := by
    apply div_nonneg
    · norm_num
    · exact le_of_lt h_pos

  have hp1_nonneg : (0 : ℝ) ≤ 1 := by norm_num
  have hp2_nonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n

  have am_gm := Real.geom_mean_le_arith_mean2_weighted hw1_nonneg hw2_nonneg hp1_nonneg hp2_nonneg weight1

  
  have geom_simp : (1 : ℝ) ^ ((n - 1 : ℝ) / n) * (n : ℝ) ^ ((1 : ℝ) / n) = (n : ℝ) ^ ((1 : ℝ) / n) := by
    rw [Real.one_rpow, one_mul]

  
  have arith_simp : ((n - 1 : ℝ) / n) * 1 + ((1 : ℝ) / n) * n = 2 - (1 : ℝ) / n := by
    field_simp [h_ne_zero]
    ring

  
  rw [← geom_simp, ← arith_simp]
  exact am_gm
