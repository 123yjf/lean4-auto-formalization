import Std.Tactic.Decide
import Mathlib.Tactic







def removeToMakePilesOfTen (n : ℕ) : ℕ := n % 10


 theorem mathd_numbertheory_254_answer :
  removeToMakePilesOfTen (239 + 174 + 83) = 6 := by
  decide


 theorem ten_dvd_sub_mod (n : ℕ) : 10 ∣ n - n % 10 := by
  refine ⟨n / 10, ?_⟩
  have h := Nat.mod_add_div n 10
  calc
    n - n % 10 = (n % 10 + 10 * (n / 10)) - n % 10 := by
      simpa [h]
    _ = 10 * (n / 10) := by
      simpa using (Nat.add_sub_cancel (n % 10) (10 * (n / 10)))




 theorem mathd_numbertheory_254_remove_divisible :
   10 ∣ (239 + 174 + 83) - 6 := by


 theorem mathd_numbertheory_254_exact :
  (239 + 174 + 83) - 6 = 10 * 49 := by
  decide

  
  have hrem : (239 + 174 + 83) % 10 = 6 := by decide
  simpa [hrem] using ten_dvd_sub_mod (239 + 174 + 83)



def pilesOfTen (n : ℕ) : Prop := ∃ k, n = 10 * k


 theorem mathd_numbertheory_254_piles :
  pilesOfTen ((239 + 174 + 83) - 6) := by
  exact ⟨49, by decide⟩
