import Std.Tactic.Decide
import Mathlib.Data.ZMod.Basic


 theorem mathd_numbertheory_229_mod :
  Nat.ModEq 7 (5^30) 1 := by
  decide


 theorem mathd_numbertheory_229_zmod :
  ((5 : ZMod 7) ^ 30) = 1 := by
  decide


 theorem mathd_numbertheory_229_rem :
  (5^30) % 7 = 1 := by
  decide
