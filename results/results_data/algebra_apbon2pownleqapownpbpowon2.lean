import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Finset.Basic


theorem arithmetic_geometric_power_inequality (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
  ((a + b) / 2) ^ n ≤ (a ^ n + b ^ n) / 2 := by
  
  have h_convex : ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := convexOn_pow n
  
  have ha_mem : a ∈ Set.Ici 0 := le_of_lt ha
  have hb_mem : b ∈ Set.Ici 0 := le_of_lt hb
  
  have h_conv_def := h_convex.2 ha_mem hb_mem (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) + 1/2 = 1)
  
  simp at h_conv_def
  convert h_conv_def using 1
  · ring
  · ring


lemma power_function_convex (n : ℕ) :
  ConvexOn ℝ (Set.Ici 0) (fun x : ℝ => x ^ n) := by
  exact convexOn_pow n
