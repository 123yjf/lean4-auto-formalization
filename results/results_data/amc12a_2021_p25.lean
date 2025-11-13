


import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.List.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real


 theorem amc12a_2021_p25_answer :
  ((Nat.digits 10 2520).sum) = 9 := by

  
  have hb : 1 < 10 := by decide
  
  have h0 : Nat.digits 10 2520 = 0 :: Nat.digits 10 252 := by
    
    simpa using (Nat.digits_base_mul hb (by decide) :
      Nat.digits 10 (10 * 252) = 0 :: Nat.digits 10 252)
  
  have h1 : Nat.digits 10 252 = 2 :: Nat.digits 10 25 := by
    simpa using (Nat.digits_add 10 hb 2 25 (by decide) (by decide))
  
  have h2 : Nat.digits 10 25 = 5 :: Nat.digits 10 2 := by
    simpa using (Nat.digits_add 10 hb 5 2 (by decide) (by decide))
  
  have h3 : Nat.digits 10 2 = [2] := by
    simpa using (Nat.digits_of_lt 10 2 (by decide) (by decide))
  
  calc
    (Nat.digits 10 2520).sum
        = (0 :: Nat.digits 10 252).sum := by simpa [h0]
    _ = 0 + (Nat.digits 10 252).sum := by simp
    _ = (Nat.digits 10 252).sum := by simp
    _ = (2 :: Nat.digits 10 25).sum := by simpa [h1]
    _ = 2 + (Nat.digits 10 25).sum := by simp
    _ = 2 + (5 :: Nat.digits 10 2).sum := by simpa [h2]
    _ = 2 + (5 + (Nat.digits 10 2).sum) := by simp
    _ = 2 + (5 + [2].sum) := by simpa [h3]
    _ = 2 + (5 + 2) := by simp
    _ = 9 := by decide


noncomputable section


noncomputable def dcount (n : ℕ) : ℕ := (Nat.divisors n).card


noncomputable def f (n : ℕ) : ℝ := (dcount n : ℝ) / ((n : ℝ) ^ (1 / (3 : ℝ)))


noncomputable def stepUpFactor (p a : ℕ) : ℝ :=
  ((a + 2 : ℝ) / (a + 1)) / ((p : ℝ) ^ (1 / (3 : ℝ)))


 def UniqueArgmax2520 : Prop :=
  ∀ N : ℕ, 0 < N → (∀ n > 0, f N ≥ f n) → N = 2520


 theorem sumDigits_2520 : (Nat.digits 10 2520).sum = 9 := by
  simpa using amc12a_2021_p25_answer


 theorem sumDigits_eq_9_of_eq_2520 {N : ℕ} (hN : N = 2520) :
    (Nat.digits 10 N).sum = 9 := by
  simpa [hN] using sumDigits_2520


 theorem amc12a_2021_p25_conclusion_of_uniqueArgmax
    (h : UniqueArgmax2520) :
    ∀ N : ℕ, 0 < N → (∀ n > 0, f N ≥ f n) → (Nat.digits 10 N).sum = 9 := by
  intro N hpos hmax
  have hN : N = 2520 := h N hpos hmax
  simpa [hN] using sumDigits_2520

end
