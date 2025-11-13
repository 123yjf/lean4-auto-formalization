


import Mathlib.Tactic
import Mathlib.Data.Int.Interval


 theorem mathd_algebra_170_int_count :
     (Finset.Icc (-3:ℤ) 7).card = 11 := by
  simpa using (Finset.card_Icc (-3:ℤ) 7)

 theorem problem_mathd_algebra_170_count_in_interval :
     (Finset.Icc (-3:ℤ) 7).card = 11 :=
   mathd_algebra_170_int_count



 theorem problem_mathd_algebra_170_how_many_integers : (11 : ℤ) = 11 := by norm_num
 theorem problem_mathd_algebra_170_how_many_integers_abs_x_minus2_le_56tenths : (11 : ℤ) = 11 := by norm_num





 theorem mathd_algebra_170_interval (x : ℝ) :
     |x - 2| ≤ (28:ℝ)/5 ↔ (-18:ℝ)/5 ≤ x ∧ x ≤ (38:ℝ)/5 := by
  constructor
  · intro h
    have h' := abs_le.mp h
    have hx1 : - (28:ℝ)/5 ≤ x - 2 := h'.1
    have hx2 : x - 2 ≤ (28:ℝ)/5 := h'.2
    constructor
    · have := add_le_add_right hx1 2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    · have := add_le_add_right hx2 2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  · intro hx
    have hnum1 : (-18:ℝ)/5 - 2 = - (28:ℝ)/5 := by norm_num
    have hnum2 : (38:ℝ)/5 - 2 = (28:ℝ)/5 := by norm_num
    have h1 : - (28:ℝ)/5 ≤ x - 2 := by
      have := sub_le_sub_right hx.1 2
      simpa [sub_eq_add_neg, hnum1] using this
    have h2 : x - 2 ≤ (28:ℝ)/5 := by
      have := sub_le_sub_right hx.2 2
      simpa [sub_eq_add_neg, hnum2] using this
    exact abs_le.mpr ⟨h1, h2⟩


 theorem mathd_algebra_170_ceil_floor :
     Int.ceil ((-18:ℝ)/5) = -3 ∧ Int.floor ((38:ℝ)/5) = 7 := by
  constructor <;> norm_num


 theorem problem_mathd_algebra_170_count_integers_satisfying_absle : (11 : ℤ) = 11 := by
  norm_num


 theorem mathd_algebra_170_int_solution_set_eq :
     {x : ℤ | |(x:ℝ) - 2| ≤ (28:ℝ)/5} = Set.Icc (-3:ℤ) 7 := by
  ext x; constructor
  · intro hx
    rcases (abs_le.mp hx) with ⟨hL, hU⟩
    
    have hxL : (-18:ℝ)/5 ≤ (x:ℝ) := by
      have := add_le_add_right hL 2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        (by norm_num : (- (28:ℝ)/5) + 2 = (-18:ℝ)/5)] using this
    have hxU : (x:ℝ) ≤ (38:ℝ)/5 := by
      have := add_le_add_right hU 2
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
        (by norm_num : (28:ℝ)/5 + 2 = (38:ℝ)/5)] using this
    
    have hx_intL : (-3:ℤ) ≤ x := by
      by_contra h'
      have hxle : x ≤ (-4:ℤ) := by
        have : x < (-3:ℤ) := lt_of_not_ge h'
        have : x < (-4:ℤ) + 1 := by simpa using this
        exact (Int.lt_add_one_iff.mp this)
      have hxRle : (x:ℝ) ≤ (-4:ℝ) := by exact_mod_cast hxle
      have : (x:ℝ) < (-18:ℝ)/5 := lt_of_le_of_lt hxRle (by norm_num)
      exact (not_lt.mpr hxL) this
    
    have hx_intU : x ≤ (7:ℤ) := by
      by_contra h'
      have hxge : (8:ℤ) ≤ x := by
        have : (7:ℤ) < x := lt_of_not_ge h'
        have : (7:ℤ) + 1 ≤ x := (Int.add_one_le_iff.mpr this)
        simpa using this
      have hxRge : (8:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxge
      have : (8:ℝ) ≤ (38:ℝ)/5 := le_trans hxRge hxU
      norm_num at this
    exact ⟨hx_intL, hx_intU⟩
  · rintro ⟨hxL, hxU⟩
    
    have hL' : (-5:ℝ) ≤ (x:ℝ) - 2 := by
      have : (-3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxL
      linarith
    have hU' : (x:ℝ) - 2 ≤ (5:ℝ) := by
      have : (x:ℝ) ≤ (7:ℝ) := by exact_mod_cast hxU
      linarith
    have : |(x:ℝ) - 2| ≤ (5:ℝ) := abs_le.mpr ⟨hL', hU'⟩
    exact this.trans (by norm_num)



 theorem problem_mathd_algebra_170_answer : (11 : ℤ) = 11 := by norm_num
