import Mathlib.Tactic


lemma cube_of_97 : 97^3 = 912673 := by decide


lemma bounds_912673 : 90^3 < 912673 \/\ 912673 < 100^3 := by decide


lemma units_digit_97 : 97 % 10 = 7 := by decide


lemma seven_cube_mod10 : 7^3 % 10 = 3 := by decide


lemma bound_left : 90^3 < 912673 := by norm_num
lemma bound_right : 912673 < 100^3 := by norm_num


lemma cube_97 : (97 : Nat) ^ 3 = 912673 := by norm_num


 theorem mathd_numbertheory_234_findN :
     ∃ N : Nat, 10 ≤ N ∧ N < 100 ∧ N ^ 3 = 912673 := by
   exact ⟨97, by decide, by decide, by decide⟩


 theorem mathd_numbertheory_234_digitsum : (97 / 10 + 97 % 10) = 16 := by
   decide





lemma last_digit_target : 912673 % 10 = 3 := by decide


lemma only_digit_seven (b : Nat) (hb : b < 10) (h : b^3 % 10 = 3) : b = 7 := by
  decide


theorem mathd_numbertheory_234_structured :
    ∃ N : Nat, 10 ≤ N ∧ N < 100 ∧ N ^ 3 = 912673 ∧ N % 10 = 7 ∧ N / 10 = 9 ∧ (N / 10 + N % 10) = 16 := by
  refine ⟨97, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide


theorem mathd_numbertheory_234_N :
    ∃ N : Nat, 10 ≤ N ∧ N < 100 ∧ N ^ 3 = 912673 ∧ (N / 10 + N % 10) = 16 := by
  exact ⟨97, by decide, by decide, by decide, by decide⟩




theorem mathd_numbertheory_234 :
    ∃ A B : Nat, 1 ≤ A ∧ A < 10 ∧ B < 10 ∧ 10 ≤ 10*A + B ∧ 10*A + B < 100 ∧ (10*A + B) ^ 3 = 912673 ∧ A + B = 16 := by
  refine ⟨9, 7, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide    
  · decide    
  · decide    
  · decide    
  · decide    
  · decide    
  · decide    


theorem mathd_numbertheory_234_simple :
    ∃ A B : Nat, (10*A + B) ^ 3 = 912673 ∧ A + B = 16 := by
  exact ⟨9, 7, by decide, by decide⟩
