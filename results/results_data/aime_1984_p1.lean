import Mathlib.Tactic

def aime_1984_p1_problem_restatement : String :=
  "In an arithmetic progression with common difference 1, the sum of the first 98 terms is 137. Find the sum of the even-indexed terms a2 + a4 + ... + a98."

def aime_1984_p1_key_idea : String :=
  "Write both the total sum of the first 98 terms and the sum of the even-indexed terms in terms of the first term a1, then eliminate a1 to get the desired sum."


theorem aime_1984_p1_even_sum
    (a1 : ℚ) (hS : 49 * (2 * a1 + 97) = 137) :
    49 * a1 + 2401 = 93 := by
  
  
  have h3 : 2 * (49 * a1 + 2401) = 49 * (2 * a1 + 97) + 49 := by
    calc
      2 * (49 * a1 + 2401)
          = 49 * (2 * a1 + 98) := by ring
      _ = 49 * (2 * a1 + 97 + 1) := by ring
      _ = 49 * (2 * a1 + 97) + 49 := by ring
  
  have h2 : 2 * (49 * a1 + 2401) = (186 : ℚ) := by
    have : (137 : ℚ) + 49 = 186 := by norm_num
    simpa [hS, this] using h3
  
  have : 2 * (49 * a1 + 2401) = 2 * 93 := by
    have : (186 : ℚ) = 2 * 93 := by norm_num
    simpa [this] using h2
  have two_ne : (2 : ℚ) ≠ 0 := by norm_num
  exact mul_left_cancel₀ two_ne this


theorem aime_1984_p1_AP_diff1_sum_even_from_total
    (a1 : ℚ)
    (h_sum_first_98_terms_AP_diff1 : 49 * (2 * a1 + 97) = 137) :
    49 * a1 + 2401 = 93 :=
  aime_1984_p1_even_sum a1 h_sum_first_98_terms_AP_diff1
