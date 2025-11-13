import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Function


theorem mathd_algebra_756 {a b : ℕ} (h1 : 2 ^ a = 32) (h2 : a ^ b = 125) : b ^ a = 243 := by
  
  have h32 : 2 ^ 5 = 32 := by norm_num
  have ha : a = 5 :=
    (Nat.pow_right_injective (a := 2) (by decide)) (by simpa [h32] using h1)
  
  subst ha
  have h125 : 5 ^ 3 = 125 := by norm_num
  have hb : b = 3 :=
    (Nat.pow_right_injective (a := 5) (by decide)) (by simpa [h125] using h2)
  subst hb
  
  norm_num
