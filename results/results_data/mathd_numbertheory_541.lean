import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


 theorem mathd_numbertheory_541 :
   ∃ a b : ℕ, 1 < a ∧ 1 < b ∧ a * b = 2005 ∧ a + b = 406 := by
   refine ⟨5, 401, ?_, ?_, ?_, ?_⟩
   · decide
   · decide
   · norm_num
   · norm_num
