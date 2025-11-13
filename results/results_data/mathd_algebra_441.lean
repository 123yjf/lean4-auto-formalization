import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Field.Basic



theorem mathd_algebra_441 : ∀ x : ℚ, x ≠ 0 → (12 / (x * x)) * (x^4 / (14 * x)) * (35 / (3 * x)) = 10 := by

  
  have step1 : ∀ x : ℚ, x ≠ 0 →
    (12 / (x * x)) * (x^4 / (14 * x)) * (35 / (3 * x)) =
    (12 * x^4 * 35) / (x * x * 14 * x * 3 * x) := by
    intros x hx
    ring

  
  have step2 : (12 : ℚ) * 35 = 420 := by
    norm_num

  
  have step3 : ∀ x : ℚ, x ≠ 0 → x * x * x * x = x^4 := by
    intros x hx
    ring

  
  have step4 : (14 : ℚ) * 3 = 42 := by
    norm_num

  
  have step5 : ∀ x : ℚ, x ≠ 0 → (420 * x^4) / (42 * x^4) = 420 / 42 := by
    intros x hx
    have h_nonzero : x^4 ≠ 0 := pow_ne_zero 4 hx
    rw [mul_div_mul_right _ _ h_nonzero]

  
  have step6 : (420 : ℚ) / 42 = 10 := by
    norm_num

  
  have step7 : ∀ x : ℚ, x ≠ 0 → x * x ≠ 0 ∧ 14 * x ≠ 0 ∧ 3 * x ≠ 0 := by
    intros x hx
    constructor
    · exact mul_ne_zero hx hx
    constructor
    · exact mul_ne_zero (by norm_num : (14 : ℚ) ≠ 0) hx
    · exact mul_ne_zero (by norm_num : (3 : ℚ) ≠ 0) hx

  
  intros x hx
  rw [step1 x hx]
  
  have h_num : (12 : ℚ) * x^4 * 35 = 420 * x^4 := by
    rw [← step2]
    ring
  have h_den : x * x * (14 : ℚ) * x * 3 * x = 42 * x^4 := by
    rw [← step4, ← step3 x hx]
    ring
  rw [h_num, h_den]
  rw [step5 x hx]
  exact step6
