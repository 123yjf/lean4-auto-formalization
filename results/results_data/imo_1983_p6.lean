














































import Mathlib.Data.Real.Basic
import Mathlib.Tactic



namespace IMO1983P6

open scoped BigOperators

noncomputable section


def E (a b c : ℝ) : ℝ :=
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a)


lemma E_at_b (b c : ℝ) : E b b c = b * c * (b - c)^2 := by
  classical
  unfold E
  ring


lemma E_at_b_nonneg {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) : 0 ≤ E b b c := by
  have hsq : 0 ≤ (b - c)^2 := by simpa using sq_nonneg (b - c)
  have hbc : 0 ≤ b * c := mul_nonneg hb hc
  simpa [E_at_b] using mul_nonneg hbc hsq

end


namespace IMO1983P6


structure TriangleSides (a b c : ℝ) : Prop :=
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (htri₁ : a < b + c) (htri₂ : b < c + a) (htri₃ : c < a + b)


def Target : Prop := ∀ ⦃a b c : ℝ⦄, TriangleSides a b c → 0 ≤ E a b c

end IMO1983P6


end IMO1983P6
