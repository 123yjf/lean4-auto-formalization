


import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


theorem mathd_numbertheory_66 : 194 % 11 = 7 := by
  
  norm_num


theorem mathd_numbertheory_66_alt : 194 % 11 = 7 := by
  
  norm_num


theorem mathd_numbertheory_66_verify : 194 % 11 = 7 := by
  
  have h_mult : 11 * 17 = 187 := by norm_num
  have h_add : 187 + 7 = 194 := by norm_num
  have h_bound : 7 < 11 := by norm_num

  
  
  norm_num
