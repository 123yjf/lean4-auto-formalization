import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp


theorem algebra_cubrtrp1oncubrtreq3_rcubp1onrcubeq5778 (r : ℝ) (hr_pos : r > 0) :
  ∀ x : ℝ, x = r^(1/3 : ℝ) → x + 1/x = 3 → r^3 + 1/r^3 = 5778 := by
  intro x hx_def h
  
  have hx_pos : x > 0 := by
    rw [hx_def]
    exact Real.rpow_pos_of_pos hr_pos _

  
  have h_cubic_expansion : x^3 + 1/x^3 = 18 := by
    
    
    have h_expand : (x + 1/x)^3 = x^3 + 1/x^3 + 3 * (x + 1/x) := by
      field_simp [hx_pos.ne']
      ring
    rw [h] at h_expand
    norm_num at h_expand
    
    have h_simp : x ^ 3 + (x ^ 3)⁻¹ = 18 := by linarith [h_expand]
    convert h_simp using 1
    simp [one_div]

  
  have h_ninth_power : x^9 + 1/x^9 = 5778 := by
    
    
    have h_expand : (x^3 + 1/x^3)^3 = x^9 + 1/x^9 + 3 * (x^3 + 1/x^3) := by
      field_simp [pow_ne_zero 3 hx_pos.ne']
      ring
    rw [h_cubic_expansion] at h_expand
    norm_num at h_expand
    
    have h_simp : x ^ 9 + (x ^ 9)⁻¹ = 5778 := by linarith [h_expand]
    convert h_simp using 1
    simp [one_div]

  
  have h_r_relation : r^3 = x^9 := by
    
    have h_x_cubed : x^3 = r := by
      rw [hx_def]
      
      
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hr_pos.le]
      norm_num
    rw [← h_x_cubed]
    ring

  have h_inv_r_relation : 1/r^3 = 1/x^9 := by
    rw [h_r_relation]

  
  convert h_ninth_power using 1
  simp [h_r_relation, h_inv_r_relation]
