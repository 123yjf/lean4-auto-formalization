import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real


 theorem mathd_algebra_196_solutions :
   {x : ℝ | |2 - x| = 3} = ({-1, 5} : Set ℝ) := by
  ext x; constructor
  · intro hx
    
    have hx' : |x - 2| = 3 := by simpa [abs_sub_comm] using hx
    
    have hsq : (x - 2) ^ 2 = (3 : ℝ) ^ 2 := by
      have := congrArg (fun t : ℝ => t ^ 2) hx'
      simpa using this
    
    have hms : (x - 2) * (x - 2) = (3 : ℝ) * 3 := by simpa [pow_two] using hsq
    have hcases : x - 2 = 3 ∨ x - 2 = -3 := by
      simpa [mul_comm] using (mul_self_eq_mul_self_iff.mp hms)
    
    have hxsol : x = -1 ∨ x = 5 := by
      cases hcases with
      | inl h => right; linarith [h]
      | inr h => left; linarith [h]
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hxsol
  · intro hx
    
    have hx' : x = -1 ∨ x = 5 := by
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hx
    cases hx' with
    | inl h =>
        
        have : 0 ≤ (3 : ℝ) := by norm_num
        simpa [h, sub_eq_add_neg, abs_of_nonneg this]
    | inr h =>
        
        have : 0 ≤ (3 : ℝ) := by norm_num
        simpa [h, sub_eq_add_neg, abs_of_nonneg this, abs_neg]


 theorem mathd_algebra_196_sum : (-1 : ℝ) + 5 = 4 := by norm_num
