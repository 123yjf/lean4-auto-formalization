import Mathlib.Data.Nat.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases


theorem mathd_numbertheory_314 :
  ∃ k : ℕ, k > 0 ∧
    (k * 1342) % 13 < 1342 % 13 ∧
    (∀ j : ℕ, j > 0 ∧ j < k → (j * 1342) % 13 ≥ 1342 % 13) ∧
    k * 1342 = 6710 := by

  
  have h_1342_mod : 1342 % 13 = 3 := by
    norm_num

  
  have h_k1_fail : (1 * 1342) % 13 ≥ 1342 % 13 := by
    simp only [one_mul]
    rfl

  have h_k2_fail : (2 * 1342) % 13 ≥ 1342 % 13 := by
    rw [h_1342_mod]
    norm_num

  have h_k3_fail : (3 * 1342) % 13 ≥ 1342 % 13 := by
    rw [h_1342_mod]
    norm_num

  have h_k4_fail : (4 * 1342) % 13 ≥ 1342 % 13 := by
    rw [h_1342_mod]
    norm_num

  
  have h_k5_works : (5 * 1342) % 13 < 1342 % 13 := by
    rw [h_1342_mod]
    norm_num

  
  have h_computation : 5 * 1342 = 6710 := by
    norm_num

  
  use 5
  constructor
  · norm_num  
  constructor
  · exact h_k5_works
  constructor
  · intro j hj
    have hj_pos : j > 0 := hj.1
    have hj_bound : j < 5 := hj.2
    interval_cases j using hj_pos, hj_bound
    · exact h_k1_fail
    · exact h_k2_fail
    · exact h_k3_fail
    · exact h_k4_fail
  · exact h_computation
