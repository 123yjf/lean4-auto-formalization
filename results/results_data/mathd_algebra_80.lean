import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Data.Rat.Defs



theorem mathd_algebra_80 : ∃! x : ℚ, x ≠ -1 ∧ (x - 9) / (x + 1) = 2 := by

  
  have step1 : ∀ x : ℚ, x = -1 → (x + 1 = 0) := by
    intros x h
    rw [h]
    ring

  
  have step2 : ∀ x : ℚ, x ≠ -1 → ((x - 9) / (x + 1) = 2 ↔ x - 9 = 2 * (x + 1)) := by
    intros x hx
    have h_nonzero : x + 1 ≠ 0 := by
      intro h
      have : x = -1 := by linarith
      exact hx this
    rw [div_eq_iff h_nonzero]

  
  have step3 : ∀ x : ℚ, 2 * (x + 1) = 2 * x + 2 := by
    intros x
    ring

  
  have step4 : ∀ x : ℚ, x - 9 = 2 * x + 2 ↔ x = -11 := by
    intros x
    constructor
    · intro h
      linarith
    · intro h
      rw [h]
      ring

  
  have step5 : (-11 : ℚ) ≠ -1 ∧ ((-11 : ℚ) - 9) / ((-11 : ℚ) + 1) = 2 := by
    constructor
    · norm_num
    · norm_num

  
  have step6 : ∀ x : ℚ, x ≠ -1 ∧ (x - 9) / (x + 1) = 2 → x = -11 := by
    intros x h
    have hx_ne := h.1
    have hx_eq := h.2
    have h1 := step2 x hx_ne
    rw [h1] at hx_eq
    rw [step3] at hx_eq
    exact (step4 x).mp hx_eq

  
  use -11, step5, step6
