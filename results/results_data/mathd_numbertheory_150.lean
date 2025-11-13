import Mathlib.Tactic
import Mathlib.Data.Nat.Prime


theorem mathd_numbertheory_150_composite :
    ∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ 7 + 30 * 6 = a * b := by
  refine ⟨11, 17, ?_, ?_, ?_⟩
  · decide
  · decide
  · norm_num


theorem mathd_numbertheory_150_min :
    (∃ a b : ℕ, 2 ≤ a ∧ 2 ≤ b ∧ 7 + 30 * 6 = a * b) ∧
    (∀ n : ℕ, 1 ≤ n → n ≤ 5 → Nat.Prime (7 + 30 * n)) := by
  constructor
  · exact mathd_numbertheory_150_composite
  · intro n hn hle
    have hI : 1 ≤ n ∧ n ≤ 5 := ⟨hn, hle⟩
    
    interval_cases n using hI <;> decide
