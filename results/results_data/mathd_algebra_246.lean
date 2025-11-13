

import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

variable {R : Type*} [CommRing R]

def f (a b x : R) : R := a * x^4 - b * x^2 + x + 5

theorem mathd_algebra_246 (a b : R) (h : f a b (-3) = 2) : f a b 3 = 8 := by
  
  have symmetry : ∀ x, f a b x - f a b (-x) = 2 * x := by
    intro x
    unfold f
    ring
  
  have h1 : f a b 3 - f a b (-3) = 2 * 3 := by exact symmetry 3
  
  have h2 : f a b 3 - f a b (-3) = 6 := by rw [h1]; norm_num
  
  have h3 : f a b 3 - 2 = 6 := by rw [h] at h2; exact h2
  
  have h4 : f a b 3 = 2 + 6 := by
    rw [← h3]
    ring
  have h5 : (2 : R) + 6 = 8 := by norm_num
  rw [h4, h5]
