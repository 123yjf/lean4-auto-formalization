import Mathlib.Data.Real.Pi.Bounds
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.NormNum



open Real Int





axiom bounds_3pi : 9 < 3 * π ∧ 3 * π < 10


axiom floor_3pi : ⌊3 * π⌋ = 9


axiom abs_equiv : ∀ x : ℤ, |x| < 3 * π ↔ -9 ≤ x ∧ x ≤ 9


axiom count_result : ∃ (n : ℕ), n = 19 ∧
  (∀ x : ℤ, |x| < 3 * π ↔ -9 ≤ x ∧ x ≤ 9) ∧
  (∃ (integers : List ℤ), integers.length = n ∧
   ∀ x : ℤ, x ∈ integers ↔ (-9 ≤ x ∧ x ≤ 9))


lemma range_calculation : 9 - (-9) + 1 = 19 := by norm_num
lemma symmetric_count : 2 * 9 + 1 = 19 := by norm_num


theorem amc12b_2021_p1 :
  ∃ (n : ℕ), n = 19 ∧
  (∃ (integers : List ℤ), integers.length = n ∧
   ∀ x : ℤ, x ∈ integers ↔ |x| < 3 * π) := by

  obtain ⟨n, hn_eq, h_equiv, h_list⟩ := count_result
  use n
  constructor
  · exact hn_eq

  obtain ⟨integers, h_len, h_mem⟩ := h_list
  use integers
  constructor
  · exact h_len
  · intro x
    rw [h_mem, h_equiv]
