import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum





def f (x : ℝ) : ℝ := 2 * x - 3
def g (x : ℝ) : ℝ := x + 1


theorem mathd_algebra_346 : g (f 5 - 1) = 7 := by
  
  unfold f g
  norm_num


lemma f_at_5 : f 5 = 7 := by
  unfold f
  norm_num


lemma f_5_minus_1 : f 5 - 1 = 6 := by
  rw [f_at_5]
  norm_num


lemma g_at_6 : g 6 = 7 := by
  unfold g
  norm_num


lemma f_def_check (x : ℝ) : f x = 2 * x - 3 := by
  unfold f
  rfl


lemma g_def_check (x : ℝ) : g x = x + 1 := by
  unfold g
  rfl


lemma direct_computation : g (f 5 - 1) = g (2 * 5 - 3 - 1) := by
  unfold f
  norm_num


lemma arithmetic_steps : 2 * 5 = 10 ∧ 10 - 3 = 7 ∧ 7 - 1 = 6 ∧ 6 + 1 = 7 := by
  norm_num
