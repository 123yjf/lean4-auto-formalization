import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring


theorem units_digit_odd_product : (1 * 3 * 5 * 7 * 9 * 11 * 13) % 10 = 5 := by
  
  
  norm_num


lemma five_times_odd_mod_ten (n : ℕ) (h : n % 2 = 1) : (5 * n) % 10 = 5 := by
  
  
  
  have : ∃ k, n = 2 * k + 1 := by
    rw [← Nat.mod_add_div n 2]
    rw [h]
    use n / 2
    ring
  obtain ⟨k, hk⟩ := this
  rw [hk]
  ring_nf
  rw [Nat.add_mod, Nat.mul_mod]
  norm_num


lemma step1 : (1 * 3) % 10 = 3 := by
  
  norm_num

lemma step2 : (3 * 5) % 10 = 5 := by
  
  norm_num

lemma step3 : (5 * 7) % 10 = 5 := by
  
  apply five_times_odd_mod_ten
  norm_num

lemma step4 : (5 * 9) % 10 = 5 := by
  
  apply five_times_odd_mod_ten
  norm_num

lemma step5 : (5 * 11) % 10 = 5 := by
  
  apply five_times_odd_mod_ten
  norm_num

lemma step6 : (5 * 13) % 10 = 5 := by
  
  apply five_times_odd_mod_ten
  norm_num
