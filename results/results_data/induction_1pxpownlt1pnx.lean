import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith


theorem bernoulli_inequality (n : ℕ) (x : ℝ) (hn : n ≥ 1) (hx : x > -1) :
  1 + n * x ≤ (1 + x) ^ n := by
  
  
  have h_ge_neg_two : -2 ≤ x := by linarith [hx]
  exact one_add_mul_le_pow h_ge_neg_two n
