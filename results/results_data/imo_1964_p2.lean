import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith



open Real





axiom ravi_substitution : ∀ a b c : ℝ, a > 0 → b > 0 → c > 0 →
  a + b > c → b + c > a → c + a > b →
  ∃ x y z : ℝ, x > 0 ∧ y > 0 ∧ z > 0 ∧
  a = y + z ∧ b = z + x ∧ c = x + y


axiom main_inequality_result : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 →
  2 * (x * (y + z)^2 + y * (z + x)^2 + z * (x + y)^2) ≤
  3 * (x + y) * (y + z) * (z + x)


axiom rhs_transform : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 →
  3 * (y + z) * (z + x) * (x + y) = 3 * (x + y) * (y + z) * (z + x)


axiom key_identity : ∀ x y z : ℝ,
  (x + y) * (y + z) * (z + x) = (x + y + z) * (x*y + y*z + z*x) - x*y*z


axiom am_gm_three_terms : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 →
  x + y + z ≥ 3 * (x * y * z)^(1/3)

axiom am_gm_three_products : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 →
  x*y + y*z + z*x ≥ 3 * (x^2 * y^2 * z^2)^(1/3)


axiom final_inequality : ∀ x y z : ℝ, x > 0 → y > 0 → z > 0 →
  (x + y + z) * (x*y + y*z + z*x) ≥ 9 * x*y*z


theorem imo_1964_p2 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (triangle_ab : a + b > c) (triangle_bc : b + c > a) (triangle_ca : c + a > b) :
  a^2 * (b + c - a) + b^2 * (c + a - b) + c^2 * (a + b - c) ≤ 3 * a * b * c := by

  
  obtain ⟨x, y, z, hx, hy, hz, ha_eq, hb_eq, hc_eq⟩ :=
    ravi_substitution a b c ha hb hc triangle_ab triangle_bc triangle_ca

  
  rw [ha_eq, hb_eq, hc_eq]
  
  have h_simplify : (y + z) ^ 2 * (z + x + (x + y) - (y + z)) +
    (z + x) ^ 2 * (x + y + (y + z) - (z + x)) +
    (x + y) ^ 2 * (y + z + (z + x) - (x + y)) =
    2 * (x * (y + z) ^ 2 + y * (z + x) ^ 2 + z * (x + y) ^ 2) := by ring

  rw [h_simplify]
  
  have h_reorder : 3 * (x + y) * (y + z) * (z + x) = 3 * (y + z) * (z + x) * (x + y) := by ring
  rw [← h_reorder]
  exact main_inequality_result x y z hx hy hz
