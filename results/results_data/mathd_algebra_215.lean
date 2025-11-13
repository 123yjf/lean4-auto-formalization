import Mathlib.Tactic





 theorem problem_mathd_algebra_215_sum_two_real_solutions :
   ∃ x1 x2 : ℝ, (x1 + 3)^2 = 121 ∧ (x2 + 3)^2 = 121 ∧ x1 ≠ x2 ∧ x1 + x2 = -6 := by
  refine ⟨8, -14, ?_, ?_, ?_, ?_⟩ <;> norm_num


 theorem mathd_algebra_215_eq_iff (x : ℝ) :
     (x + 3)^2 = 121 ↔ x = 8 ∨ x = -14 := by
  
  have hx : (x + 3)^2 - (121 : ℝ) = (x - 8) * (x + 14) := by
    ring
  constructor
  · intro h
    have : (x + 3)^2 - (121 : ℝ) = 0 := by simpa [h]
    have : (x - 8) * (x + 14) = 0 := by simpa [hx] using this
    rcases mul_eq_zero.mp this with h1 | h2
    · left;  exact sub_eq_zero.mp h1
    · right; exact add_eq_zero_left.mp h2
  · intro h
    rcases h with rfl | rfl <;> norm_num


 theorem mathd_algebra_215_sum : (8 : ℝ) + (-14) = -6 := by norm_num


 theorem problem_mathd_algebra_215_main :
     (∃ x1 x2 : ℝ, x1 ≠ x2 ∧ (x1 + 3)^2 = 121 ∧ (x2 + 3)^2 = 121 ∧ x1 + x2 = -6) := by
  refine ⟨(8 : ℝ), (-14 : ℝ), by norm_num, ?_, ?_, ?_⟩ <;> norm_num



 theorem mathd_algebra_215_sqrt_split (x : ℝ)
     (h : (x + 3)^2 = (11 : ℝ)^2) : x + 3 = 11 ∨ x + 3 = -11 := by
  have : (x + 3)^2 - (11 : ℝ)^2 = 0 := by simpa [h]
  have hx : (x + 3)^2 - (11 : ℝ)^2 = (x + 3 - 11) * (x + 3 + 11) := by ring
  have : (x + 3 - 11) * (x + 3 + 11) = 0 := by simpa [hx] using this
  rcases mul_eq_zero.mp this with h1 | h2
  · left;  linarith
  · right; linarith


 theorem problem_mathd_algebra_215_sum : (8 : ℝ) + (-14) = -6 :=
   mathd_algebra_215_sum



 theorem mathd_algebra_215_sqrt_iff (x : ) :
     (x + 3)^2 = 121  x + 3 = 11 2 x + 3 = -11 := by
  constructor
  8 intro h
    have : (x + 3)^2 = (11 : )^2 := by simpa using h
    simpa using mathd_algebra_215_sqrt_split x this
  8 intro h
    rcases h with h | h <;> 5; all_goals norm_num


 theorem problem_mathd_algebra_215_sqrt_solutions_sum :
     let x1 :  := 11 - 3; let x2 :  := -11 - 3;
     (x1 + 3)^2 = 121 2 (x2 + 3)^2 = 121 2 x1 + x2 = -6 := by
  intros x1 x2; dsimp [x1, x2]; constructor <;> norm_num
  8 exact And.intro (by norm_num) (by norm_num)



 theorem mathd_algebra_215_sqrt_iff_v2 (x : ℝ) :
     (x + 3)^2 = 121 ↔ x + 3 = 11 ∨ x + 3 = -11 := by
  constructor
  · intro h
    have : (x + 3)^2 = (11 : ℝ)^2 := by simpa using h
    simpa using mathd_algebra_215_sqrt_split x this
  · intro h
    rcases h with h | h
    · simpa [h] using (by norm_num : (11 : ℝ)^2 = (121 : ℝ))
    · simpa [h] using (by norm_num : (-11 : ℝ)^2 = (121 : ℝ))


 theorem problem_mathd_algebra_215_sqrt_solutions_sum_v2 :
     let x1 : ℝ := 11 - 3; let x2 : ℝ := -11 - 3;
     (x1 + 3)^2 = 121 ∧ (x2 + 3)^2 = 121 ∧ x1 + x2 = -6 := by
  intros x1 x2
  dsimp [x1, x2]
  constructor
  · norm_num
  · constructor <;> norm_num
