import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring




def base_nine_852_standard : ℕ := 8 * 9^2 + 5 * 9^1 + 2 * 9^0


def base_nine_852_horner : ℕ := ((8 * 9 + 5) * 9 + 2)


theorem mathd_numbertheory_207 : base_nine_852_standard = 695 := by

  
  have step1 : base_nine_852_standard = 8 * 9^2 + 5 * 9^1 + 2 * 9^0 := by
    unfold base_nine_852_standard
    rfl

  
  have step2_powers : 9^2 = 81 ∧ 9^1 = 9 ∧ 9^0 = 1 := by
    norm_num

  
  have step3_products : 8 * 81 = 648 ∧ 5 * 9 = 45 ∧ 2 * 1 = 2 := by
    norm_num

  
  have step4_sum : 648 + 45 + 2 = 695 := by
    norm_num

  
  have step5_combine : 8 * 9^2 + 5 * 9^1 + 2 * 9^0 = 695 := by
    norm_num

  
  rw [step1, step5_combine]


theorem horner_method_verification : base_nine_852_horner = 695 := by

  
  have step6_horner1 : 8 * 9 + 5 = 77 := by
    norm_num

  
  have step7_horner2 : 77 * 9 + 2 = 695 := by
    norm_num

  
  have step8_horner_combine : ((8 * 9 + 5) * 9 + 2) = 695 := by
    norm_num

  
  unfold base_nine_852_horner
  exact step8_horner_combine


theorem base_conversion_equivalence : base_nine_852_standard = base_nine_852_horner := by

  
  have h1 : base_nine_852_standard = 695 := mathd_numbertheory_207
  have h2 : base_nine_852_horner = 695 := horner_method_verification

  
  rw [h1, h2]
