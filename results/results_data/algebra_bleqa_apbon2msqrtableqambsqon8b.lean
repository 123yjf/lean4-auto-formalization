import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

theorem inequality_am_gm_variant (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) :
  (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
  
  let t := Real.sqrt a
  let s := Real.sqrt b
  have ht_pos : 0 < t := Real.sqrt_pos.mpr ha
  have hs_pos : 0 < s := Real.sqrt_pos.mpr hb
  have ht_sq : t^2 = a := Real.sq_sqrt (le_of_lt ha)
  have hs_sq : s^2 = b := Real.sq_sqrt (le_of_lt hb)
  have hts : s ≤ t := Real.sqrt_le_sqrt hab

  
  have lhs_transform : 8 * s^2 * ((a + b) / 2 - Real.sqrt (a * b)) = 4 * s^2 * (t - s)^2 := by
    rw [← ht_sq, ← hs_sq]
    rw [Real.sqrt_mul (sq_nonneg t) (s^2)]
    rw [Real.sqrt_sq ht_pos.le, Real.sqrt_sq hs_pos.le]
    ring

  
  have rhs_transform : (a - b)^2 = (t + s)^2 * (t - s)^2 := by
    rw [← ht_sq, ← hs_sq]
    ring

  
  have core_ineq : 4 * s^2 ≤ (t + s)^2 := by
    calc (t + s)^2
      = t^2 + 2*t*s + s^2 := by ring
      _ ≥ s^2 + 2*s*s + s^2 := by
        have h1 : t^2 ≥ s^2 := by
          rw [sq, sq]
          exact mul_self_le_mul_self (le_of_lt hs_pos) hts
        have h2 : 2*t*s ≥ 2*s*s := by
          have h_eq1 : (2:ℝ) * t * s = 2 * (t * s) := by ring
          have h_eq2 : (2:ℝ) * s * s = 2 * (s * s) := by ring
          rw [h_eq1, h_eq2]
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hts (le_of_lt hs_pos)
          · norm_num
        linarith [h1, h2]
      _ = 4*s^2 := by ring

  
  have h_cancel : 8 * s^2 * ((a + b) / 2 - Real.sqrt (a * b)) ≤ (a - b)^2 := by
    rw [lhs_transform, rhs_transform]
    apply mul_le_mul_of_nonneg_right core_ineq
    exact sq_nonneg (t - s)

  
  have h_eq : 8 * s^2 = 8 * b := by rw [← hs_sq]
  rw [h_eq] at h_cancel

  have hb8_pos : 0 < 8 * b := by
    apply mul_pos
    · norm_num
    · exact hb

  have h_final : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) := by
    have : (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b)^2 / (8 * b) ↔
           8 * b * ((a + b) / 2 - Real.sqrt (a * b)) ≤ (a - b)^2 := by
      rw [le_div_iff₀ hb8_pos]
      rw [mul_comm]
    rw [this]
    exact h_cancel
  exact h_final
