

import Mathlib.Tactic.NormNum.Basic


def f (x : ℕ) : ℕ := x + 1
def g (x : ℕ) : ℕ := x^2 + 3


lemma g_at_2 : g 2 = 7 := by
  simp [g]


theorem mathd_algebra_143 : f (g 2) = 8 := by
  rw [g_at_2]
  simp [f]


lemma comp_formula (x : ℕ) : (f ∘ g) x = x^2 + 4 := by
  simp [Function.comp, f, g]


theorem mathd_algebra_143_alt : (f ∘ g) 2 = 8 := by
  rw [comp_formula]
  simp
