import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic






theorem aime_1983_p1 (x y z w : ℝ)
  (hx : x > 1) (hy : y > 1) (hz : z > 1)
  (h1 : Real.log w / Real.log x = 24)
  (h2 : Real.log w / Real.log y = 40)
  (h3 : Real.log w / Real.log (x * y * z) = 12) :
  Real.log w / Real.log z = 60 := by
  
  have hx_pos : x > 0 := by linarith
  have hy_pos : y > 0 := by linarith
  have hz_pos : z > 0 := by linarith
  have hxyz_pos : x * y * z > 0 := by
    apply mul_pos
    apply mul_pos hx_pos hy_pos
    exact hz_pos

  
  have hlog_x_pos : Real.log x > 0 := Real.log_pos hx
  have hlog_y_pos : Real.log y > 0 := Real.log_pos hy
  have hlog_z_pos : Real.log z > 0 := Real.log_pos hz
  have hlog_x_ne_zero : Real.log x ≠ 0 := ne_of_gt hlog_x_pos
  have hlog_y_ne_zero : Real.log y ≠ 0 := ne_of_gt hlog_y_pos
  have hlog_z_ne_zero : Real.log z ≠ 0 := ne_of_gt hlog_z_pos

  
  have eq1 : Real.log w = 24 * Real.log x := by
    rw [div_eq_iff] at h1
    exact h1
    exact hlog_x_ne_zero

  
  have eq2 : Real.log w = 40 * Real.log y := by
    rw [div_eq_iff] at h2
    exact h2
    exact hlog_y_ne_zero

  
  have hxyz_gt_one : x * y * z > 1 := by
    have h_xy : x * y > 1 := by
      have : x * y > 1 * 1 := by
        apply mul_lt_mul' (le_of_lt hx) hy (by norm_num) hx_pos
      simp at this
      exact this
    have : x * y * z > 1 * z := by
      apply mul_lt_mul_of_pos_right h_xy hz_pos
    have : 1 * z = z := by ring
    rw [this] at this
    have : z > 1 := hz
    linarith

  have hlog_xyz_ne_zero : Real.log (x * y * z) ≠ 0 := by
    apply Real.log_ne_zero.mpr
    constructor
    · exact ne_of_gt hxyz_pos
    constructor
    · exact ne_of_gt hxyz_gt_one
    · linarith

  have eq3 : Real.log w = 12 * Real.log (x * y * z) := by
    rw [div_eq_iff] at h3
    exact h3
    exact hlog_xyz_ne_zero

  
  
  have rel_y : Real.log y = (3/5) * Real.log x := by
    have : 24 * Real.log x = 40 * Real.log y := by
      rw [←eq1, ←eq2]
    have : Real.log y = (24/40) * Real.log x := by
      have : 40 * Real.log y = 24 * Real.log x := by rw [this]
      have : Real.log y = (24 * Real.log x) / 40 := by
        rw [←this]
        field_simp [hlog_y_ne_zero]
      rw [this]
      ring
    norm_num at this
    exact this

  
  
  
  
  have rel_z : Real.log z = Real.log x - Real.log y := by
    have : Real.log (x * y * z) = Real.log x + Real.log y + Real.log z := by
      rw [Real.log_mul (ne_of_gt (mul_pos hx_pos hy_pos)) (ne_of_gt hz_pos), Real.log_mul (ne_of_gt hx_pos) (ne_of_gt hy_pos)]
    rw [this] at eq3
    have : 24 * Real.log x = 12 * (Real.log x + Real.log y + Real.log z) := by
      rw [←eq1, eq3]
    have : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by
      have h24_12 : (24 : ℝ) = 12 * 2 := by norm_num
      rw [h24_12] at this
      rw [mul_assoc] at this
      have h12_ne_zero : (12 : ℝ) ≠ 0 := by norm_num
      have : 2 * Real.log x = Real.log x + Real.log y + Real.log z := by
        have : 12 * (2 * Real.log x) = 12 * (Real.log x + Real.log y + Real.log z) := this
        have : (12 * (2 * Real.log x)) / 12 = (12 * (Real.log x + Real.log y + Real.log z)) / 12 := by
          rw [this]
        simp [h12_ne_zero] at this
        exact this
      exact this
    linarith

  
  have rel_z_simplified : Real.log z = (2/5) * Real.log x := by
    rw [rel_z, rel_y]
    ring

  
  rw [eq1, rel_z_simplified]
  have : Real.log x ≠ 0 := hlog_x_ne_zero
  have h2_5_ne_zero : (2/5 : ℝ) ≠ 0 := by norm_num
  field_simp [this, h2_5_ne_zero]
  ring
