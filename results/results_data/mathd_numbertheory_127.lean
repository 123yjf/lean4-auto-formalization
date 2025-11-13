import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


theorem mathd_numbertheory_127 :
  (Finset.sum (Finset.range 101) (fun i => 2^i)) % 7 = 3 := by

  
  have h_geom_sum : Finset.sum (Finset.range 101) (fun i => 2^i) = 2^101 - 1 := by
    
    rw [Nat.geomSum_eq (by norm_num : 2 ≤ 2) 101]
    simp

  
  have h_period : (2^3 : ℕ) % 7 = 1 := by
    
    norm_num

  
  have h_101_mod : (2^101 : ℕ) % 7 = 4 := by
    
    norm_num

  
  rw [h_geom_sum]
  
  have h_final : (2^101 - 1) % 7 = 3 := by
    
    norm_num [h_101_mod]

  exact h_final
