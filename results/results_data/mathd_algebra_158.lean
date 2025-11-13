





import Mathlib.Tactic


lemma five_even_sum (x : ℤ) :
  x + (x+2) + (x+4) + (x+6) + (x+8) = 5 * x + 20 := by
  ring


lemma sum_first_eight_odds :
  (1+3+5+7+9+11+13+15 : ℤ) = 64 := by
  norm_num


@[simp] theorem mathd_algebra_158_unique :
  ∃! x : ℤ,
    x + (x+2) + (x+4) + (x+6) + (x+8) = ((1:ℤ)+3+5+7+9+11+13+15) - 4 := by
  refine ⟨8, ?eq, ?uniq⟩
  · 
    calc
      8 + (8+2) + (8+4) + (8+6) + (8+8)
          = 5 * (8:ℤ) + 20 := by simpa [five_even_sum]
      _ = 60 := by norm_num
      _ = ((1:ℤ)+3+5+7+9+11+13+15) - 4 := by
        simpa [sum_first_eight_odds]
  · 
    intro y hy
    have h5y20 : 5 * y + 20 = 60 := by
      simpa [five_even_sum y, sum_first_eight_odds] using hy
    have hmul : 5 * (y - 8) = 0 := by
      have : 5 * y - 5 * 8 = 0 := by
        have : 5 * y = 40 := by
          have := congrArg (fun t => t - 20) h5y20
          simpa using this
        simpa using this.trans (by norm_num : (40:ℤ) = 5 * 8)
      simpa [mul_sub, two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    rcases mul_eq_zero.mp hmul with h5 | hsub
    · have h5ne : (5:ℤ) ≠ 0 := by norm_num
      exact (h5ne h5).elim
    · simpa using hsub


@[simp] theorem mathd_algebra_158 :
  ∃ x : ℤ,
    x + (x+2) + (x+4) + (x+6) + (x+8) = ((1:ℤ)+3+5+7+9+11+13+15) - 4 ∧
    x = 8 := by
  refine ⟨8, ?_, rfl⟩
  norm_num


@[simp] theorem mathd_algebra_158_smallest_even :
  ∃ x : ℤ,
    x + (x+2) + (x+4) + (x+6) + (x+8) = ((1:ℤ)+3+5+7+9+11+13+15) - 4 ∧ x = 8 :=
by
  simpa using mathd_algebra_158



@[simp] theorem mathd_algebra_158_smallest_of_five_consecutive_even :
  ∃ x : ℤ,
    x + (x+2) + (x+4) + (x+6) + (x+8) = ((1:ℤ)+3+5+7+9+11+13+15) - 4 ∧ x = 8 :=
by
  simpa using mathd_algebra_158
