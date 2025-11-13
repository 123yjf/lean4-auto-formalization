import Mathlib.Tactic




noncomputable def overallMean (w1 w2 m1 m2 : ℝ) : ℝ :=
  (m1*w1 + m2*w2) / (w1 + w2)



noncomputable def morningMean : ℝ := 84
noncomputable def afternoonMean : ℝ := 70




noncomputable def morningClassSize : ℝ := 3
noncomputable def afternoonClassSize : ℝ := 4




theorem amc12b_2021_p4 : overallMean morningClassSize afternoonClassSize morningMean afternoonMean = 76 := by
  
  simpa [overallMean, morningMean, afternoonMean, morningClassSize, afternoonClassSize] using
    (by norm_num : ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4) = 76)


lemma amc12b_2021_p4_weighted_form :
    ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4)
      = (3/7:ℝ) * 84 + (4/7:ℝ) * 70 := by
  calc
    ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4)
        = ((84:ℝ) * 3) / (3 + 4) + ((70:ℝ) * 4) / (3 + 4) := by
          simpa using add_div ((84:ℝ) * 3) ((70:ℝ) * 4) (3 + 4 : ℝ)
    _ = (84:ℝ) * (3 / (3 + 4)) + (70:ℝ) * (4 / (3 + 4)) := by
          simp [mul_div_assoc]
    _ = (3/7:ℝ) * 84 + (4/7:ℝ) * 70 := by
          norm_num


lemma amc12b_2021_p4_q : ((84:ℚ) * 3 + (70:ℚ) * 4) / (3 + 4) = 76 := by
  norm_num



lemma overall_mean_of_morning_and_afternoon_in_ratio_3_4 :
    ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4) = 76 := by
  norm_num



lemma problem_restatement_overall_mean_score_morning_84_afternoon_70_ratio_3_4 :
    ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4) = 76 := by
  norm_num




lemma overall_mean_scaled_ratio_3k_4k (k : ℝ) (hk : k ≠ 0) :
    ((84:ℝ) * (3*k) + (70:ℝ) * (4*k)) / ((3*k) + (4*k)) = 76 := by
  have hbase : ((84:ℝ) * 3 + (70:ℝ) * 4) / ((3:ℝ) + 4) = 76 := by norm_num
  have hnum : (84:ℝ) * (3*k) + (70:ℝ) * (4*k) = (((84:ℝ) * 3 + (70:ℝ) * 4) * k) := by ring
  have hden : (3*k) + (4*k) = ((3:ℝ)+4) * k := by ring
  calc
    ((84:ℝ) * (3*k) + (70:ℝ) * (4*k)) / ((3*k) + (4*k))
        = (((84:ℝ)*3 + (70:ℝ)*4) * k) / (((3:ℝ)+4) * k) := by simpa [hnum, hden]
    _ = ((84:ℝ)*3 + (70:ℝ)*4) / ((3:ℝ)+4) := by
          field_simp [div_eq_mul_inv, hk, mul_comm, mul_left_comm, mul_assoc]
    _ = 76 := by simpa using hbase

lemma overallMean_scaled_ratio (k : ℝ) (hk : k ≠ 0) :
    overallMean (3*k) (4*k) 84 70 = 76 := by
  simpa [overallMean, mul_comm, mul_left_comm, mul_assoc]
    using overall_mean_scaled_ratio_3k_4k k hk

lemma weighted_average_morning_afternoon_ratio_3_4 :
    ((84:ℝ) * 3 + (70:ℝ) * 4) / (3 + 4)
      = (3/7:ℝ) * 84 + (4/7:ℝ) * 70 := by
  simpa using amc12b_2021_p4_weighted_form
