





import Mathlib.Tactic
open Set


def L1 : Set (ℚ × ℚ) := {p | 3 * p.2 = p.1}
def L2 : Set (ℚ × ℚ) := {p | 2 * p.1 + 5 * p.2 = 11}


@[simp] theorem mathd_algebra_329 : ∃ A : ℚ × ℚ, A ∈ L1 ∩ L2 ∧ A.1 + A.2 = 4 := by
  refine ⟨(3, 1), ?hmem, ?hsum⟩
  · 
    constructor
    · 
      norm_num [L1]
    · 
      norm_num [L2]
  · 
    norm_num
