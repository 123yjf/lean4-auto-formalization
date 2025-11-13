






import Mathlib








namespace AMC12A_2020_P10


@[simp] def n : ℕ := 256


lemma pow4_4 : 4 ^ 4 = (256 : ℕ) := by
  norm_num


 theorem amc12a_2020_p10 : 2 + 5 + 6 = 13 := by
  norm_num

end AMC12A_2020_P10


namespace AMC12A_2020_P10
noncomputable section


open Real


@[simp] def lhs (n : ℝ) : ℝ := Real.logb 2 (Real.logb 16 n)
@[simp] def rhs (n : ℝ) : ℝ := Real.logb 4 (Real.logb 4 n)


@[simp] def xR : ℝ := 4
@[simp] def nR : ℝ := 4 ^ xR


@[simp] def eqHolds256Prop : Prop := lhs 256 = rhs 256


@[simp] def digitSum256 : Prop := (2 + 5 + 6 = 13)


lemma eqHolds256 : lhs 256 = rhs 256 := by
  
  have hlog256 : Real.log (256 : ℝ) = (8 : ℕ) * Real.log (2 : ℝ) := by
    have : (256 : ℝ) = (2 : ℝ) ^ (8 : ℕ) := by norm_num
    simpa [this] using Real.log_pow (by norm_num : 0 < (2 : ℝ)) (8 : ℕ)
  have hlog4 : Real.log (4 : ℝ) = (2 : ℕ) * Real.log (2 : ℝ) := by
    have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    simpa [this] using Real.log_pow (by norm_num : 0 < (2 : ℝ)) (2 : ℕ)
  have hlog16 : Real.log (16 : ℝ) = (4 : ℕ) * Real.log (2 : ℝ) := by
    have : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
    simpa [this] using Real.log_pow (by norm_num : 0 < (2 : ℝ)) (4 : ℕ)
  have h2ne : Real.log (2 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h4ne : Real.log (4 : ℝ) ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  
  have h1 : Real.logb 4 (256 : ℝ) = 4 := by
    calc
      Real.logb 4 (256 : ℝ) = Real.log (256 : ℝ) / Real.log 4 := rfl
      _ = ((8 : ℕ) * Real.log 2) / ((2 : ℕ) * Real.log 2) := by
            simpa [hlog256, hlog4]
      _ = 4 := by
            field_simp [h2ne]; norm_num
  have h2 : Real.logb 16 (256 : ℝ) = 2 := by
    calc
      Real.logb 16 (256 : ℝ) = Real.log (256 : ℝ) / Real.log 16 := rfl
      _ = ((8 : ℕ) * Real.log 2) / ((4 : ℕ) * Real.log 2) := by
            simpa [hlog256, hlog16]
      _ = 2 := by
            field_simp [h2ne]; norm_num
  
  have hl : lhs 256 = 1 := by
    calc
      lhs 256 = Real.log (Real.logb 16 (256 : ℝ)) / Real.log 2 := rfl
      _ = Real.log 2 / Real.log 2 := by simpa [h2]
      _ = 1 := by exact div_self h2ne


  have hr : rhs 256 = 1 := by
    calc
      rhs 256 = Real.log (Real.logb 4 (256 : ℝ)) / Real.log 4 := rfl
      _ = Real.log 4 / Real.log 4 := by simpa [h1]
      _ = 1 := by exact div_self h4ne
  exact hl.trans hr.symm





lemma exists_solution_and_digit_sum :
    ∃ n : ℕ, 1 < n ∧
      Real.logb 2 (Real.logb 16 (n : ℝ)) = Real.logb 4 (Real.logb 4 (n : ℝ)) ∧
      (2 + 5 + 6 = 13) := by
  refine ⟨256, by decide, ?_, by decide⟩
  simpa using eqHolds256

end
end AMC12A_2020_P10
