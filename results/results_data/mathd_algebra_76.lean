

import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum


def f (n : ℤ) : ℤ := if Odd n then n^2 else n^2 - 4*n - 1


theorem mathd_algebra_76 : f (f (f (f (f 4)))) = 1 := by
  
  
  have step1 : f 4 = -1 := by
    simp [f, show ¬Odd (4 : ℤ) by decide]

  
  have step2 : f (-1) = 1 := by
    simp [f, show Odd (-1 : ℤ) by decide]

  
  have step3 : f 1 = 1 := by
    simp [f, show Odd (1 : ℤ) by decide]

  
  rw [step1, step2, step3, step3, step3]
