import Mathlib.Tactic




 theorem problem_mathd_algebra_359_AP_avg {y : ℚ}
     (h : (12 : ℚ) = ((y + 6) + y) / 2) : y = 9 :=
   mathd_algebra_359_avg h

 theorem problem_mathd_algebra_359_AP_diff {y : ℚ}
     (h : 12 - (y + 6) = y - 12) : y = 9 :=
   mathd_algebra_359_diff h


 theorem mathd_algebra_359_main_avg {y : } (havg : (12 : ) = ((y + 6) + y) / 2) : y = 9 :=
   mathd_algebra_359_avg havg



theorem mathd_algebra_359_diff {y : ℚ}
    (h : 12 - (y + 6) = y - 12) :
    y = 9 := by
  linarith


theorem mathd_algebra_359_avg {y : ℚ}
    (h : (12 : ℚ) = ((y + 6) + y) / 2) :
    y = 9 := by
  
  have h2 := congrArg (fun t => (2 : ℚ) * t) h
  
  have hsum : (24 : ℚ) = (y + 6) + y := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using h2
  
  have : (24 : ℚ) = 2*y + 6 := by
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hsum
  linarith



theorem mathd_algebra_359 {y : ℚ}
    (h : ∃ d, 12 - (y + 6) = d ∧ y - 12 = d) :
    y = 9 := by
  rcases h with ⟨d, hL, hR⟩
  have hdiff : 12 - (y + 6) = y - 12 := hL.trans hR.symm
  linarith


example : (12 : ℚ) - ((9 : ℚ) + 6) = 9 - (12 : ℚ) := by decide



lemma mathd_algebra_359_a_iff (y : ℚ) : 12 - (y + 6) = y - 12 ↔ y = 9 := by
  constructor
  · intro h
    have h1 : 6 - y = y - 12 := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
    linarith
  · intro hy
    subst hy
    norm_num

lemma mathd_algebra_359_b_iff (y : ℚ) : 12 = ((y + 6) + y) / 2 ↔ y = 9 := by
  constructor
  · intro h
    have h1 : (24 : ℚ) = (y + 6) + y := by
      simpa using congrArg (fun t : ℚ => 2 * t) h
    have h2 : (24 : ℚ) = 2 * y + 6 := by
      simpa [two_mul, add_comm, add_left_comm, add_assoc] using h1
    linarith
  · intro hy
    subst hy
    norm_num



lemma ap12_diff_symm_iff (y : ℚ) : 12 - (y + 6) = y - 12 ↔ y = 9 := by
  simpa using (mathd_algebra_359_a_iff y)

lemma ap12_avg_iff (y : ℚ) : 12 = ((y + 6) + y) / 2 ↔ y = 9 := by
  simpa using (mathd_algebra_359_b_iff y)

lemma ap12_exists_d_iff (y : ℚ) : (∃ d : ℚ, 12 - (y + 6) = d ∧ y - 12 = d) ↔ y = 9 := by
  simpa using (mathd_algebra_359_c_iff y)

lemma ap12_isAP_iff (y : ℚ) : isAP (y + 6) 12 y ↔ y = 9 := by
  simpa [isAP] using (mathd_algebra_359_a_iff y)



theorem arithmetic_progression_yplus6_12_y_iff_eq9 (y : ℚ) :
    isAP (y + 6) 12 y ↔ y = 9 := by
  simpa [isAP] using (mathd_algebra_359_a_iff y)

lemma ap12_avg_eq_iff (y : ℚ) : 12 = ((y + 6) + y) / 2 ↔ y = 9 := by
  constructor
  · intro h
    
    have h1 : 12 * 2 = (y + 6) + y := by
      simpa using ( (eq_div_iff_mul_eq (by decide : (2:ℚ) ≠ 0)).1 h )
    have h2 : 24 = 2 * y + 6 := by
      simpa [two_mul, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using h1
    linarith


 theorem mathd_algebra_359_main_AP {y : ℚ} (hAP : isAP (y + 6) 12 y) : y = 9 := by
  have h : 12 - (y + 6) = y - 12 := by
    simpa [isAP, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hAP
  exact mathd_algebra_359_diff (y := y) h

  · intro hy
    subst hy
    norm_num



theorem yplus6_12_y_arithmetic_progression_solve_avg {y : ℚ}
    (h : (12 : ℚ) = ((y + 6) + y) / 2) : y = 9 :=
  mathd_algebra_359_avg h

theorem yplus6_12_y_arithmetic_progression_solve_diff {y : ℚ}
    (h : 12 - (y + 6) = y - 12) : y = 9 :=
  mathd_algebra_359_diff h



theorem yplus6_12_y_arithmetic_progression_solve_avg {y : ℚ}
    (h : (12 : ℚ) = ((y + 6) + y) / 2) : y = 9 :=
  mathd_algebra_359_avg h

theorem yplus6_12_y_arithmetic_progression_solve_diff {y : ℚ}
    (h : 12 - (y + 6) = y - 12) : y = 9 :=
  mathd_algebra_359_diff h


def isAP (a b c : ℚ) : Prop := b - a = c - b


theorem mathd_algebra_359_main {y : ℚ} (h : isAP (y + 6) 12 y) : y = 9 := by
  have : 12 - (y + 6) = y - 12 := by
    simpa [isAP, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  linarith


example : isAP ((9 : ℚ) + 6) 12 (9 : ℚ) := by
  simpa [isAP] using (show (12 : ℚ) - ((9 : ℚ) + 6) = (9 : ℚ) - 12 by norm_num)
