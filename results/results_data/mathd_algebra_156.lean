import Mathlib.Data.Real.Basic
import Mathlib.Tactic











theorem mathd_algebra_156 :
    ∃ m n : ℝ, m > n ∧ m - n = 1 ∧
      {x : ℝ | x^4 = 5 * x^2 - 6} ⊆
        {x : ℝ | x = Real.sqrt m ∨ x = -Real.sqrt m ∨ x = Real.sqrt n ∨ x = -Real.sqrt n} := by
  refine ⟨3, 2, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · intro x hx
    
    have hxpoly : x^4 - 5 * x^2 + 6 = 0 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_eq_zero.mpr hx)
    have hfacx : x^4 - 5 * x^2 + 6 = (x^2 - 2) * (x^2 - 3) := by
      ring
    have hprod : (x^2 - 2) * (x^2 - 3) = 0 := by
      simpa [hfacx] using hxpoly
    have htn : x^2 = 2 ∨ x^2 = 3 := by
      rcases mul_eq_zero.mp hprod with h2 | h3
      · left;  have := sub_eq_zero.mp h2; simpa using this
      · right; have := sub_eq_zero.mp h3; simpa using this
    have h2nn : 0 ≤ (2 : ℝ) := by norm_num
    have h3nn : 0 ≤ (3 : ℝ) := by norm_num
    
    rcases htn with h2 | h3
    · have : x^2 = (Real.sqrt 2)^2 := by simpa [pow_two, Real.sq_sqrt h2nn] using h2
      have hx' : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
        simpa [pow_two] using (sq_eq_sq_iff_eq_or_eq_neg).1 this
      rcases hx' with hxpos | hxneg
      · exact Or.inr (Or.inr (Or.inl (by simpa using hxpos)))
      · exact Or.inr (Or.inr (Or.inr (by simpa using hxneg)))
    · have : x^2 = (Real.sqrt 3)^2 := by simpa [pow_two, Real.sq_sqrt h3nn] using h3
      have hx' : x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
        simpa [pow_two] using (sq_eq_sq_iff_eq_or_eq_neg).1 this
      rcases hx' with hxpos | hxneg
      · exact Or.inl (by simpa using hxpos)
      · exact Or.inr (Or.inl (by simpa using hxneg))
