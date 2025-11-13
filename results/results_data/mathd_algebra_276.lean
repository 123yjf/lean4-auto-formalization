import Mathlib.Tactic




 theorem mathd_algebra_276_factor {x : ℤ} :
     (10 * x^2 - x - 24) = (5 * x - 8) * (2 * x + 3) := by
  ring

 theorem mathd_algebra_276_AB_plus_B :
     ∃ A B : ℤ, A*B = 10 ∧ 3*A - 8*B = -1 ∧ (A*B + B) = 12 := by
  refine ⟨5, 2, ?h1, ?h2, ?h3⟩ <;> norm_num


 theorem problem_mathd_algebra_276_factor_eq {x : ℤ} :
     (10 * x^2 - x - 24) = (5 * x - 8) * (2 * x + 3) :=
   mathd_algebra_276_factor

 theorem problem_mathd_algebra_276_answer :
     ∃ A B : ℤ, A*B = 10 ∧ 3*A - 8*B = -1 ∧ (A*B + B) = 12 :=
   mathd_algebra_276_AB_plus_B


 theorem mathd_algebra_276_value : (12 : ℤ) = 12 := by
  norm_num
