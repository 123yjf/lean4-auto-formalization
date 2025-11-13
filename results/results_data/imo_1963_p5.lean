import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Data.Complex.Exponential




lemma two_sin_pi_div_seven_ne_zero : 2 * Real.sin (Real.pi / 7) ≠ 0 := by
  apply mul_ne_zero two_ne_zero
  
  apply ne_of_gt
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos Real.pi_pos (by norm_num)
  · 
    calc Real.pi / 7
      < Real.pi / 2 := by
          apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by norm_num)
      _ < Real.pi := by
          have : Real.pi / 2 < Real.pi / 1 := by
            apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by norm_num)
          rw [div_one] at this
          exact this


lemma sin_pi_mul_neg_div (a b : ℝ) : Real.sin (Real.pi * (- a / b)) = - Real.sin (Real.pi * (a / b)) := by
  ring_nf
  exact Real.sin_neg _

theorem imo_1963_p5 : Real.cos (Real.pi / 7) - Real.cos (2 * Real.pi / 7) + Real.cos (3 * Real.pi / 7) = 1 / 2 := by
  rw [← mul_right_inj' two_sin_pi_div_seven_ne_zero, mul_add, mul_sub, ← Real.sin_two_mul,
    Real.two_mul_sin_mul_cos, Real.two_mul_sin_mul_cos]
  ring_nf
  rw [← Real.sin_pi_sub (Real.pi * (3 / 7)), sin_pi_mul_neg_div 2 7, sin_pi_mul_neg_div 1 7]
  ring_nf
