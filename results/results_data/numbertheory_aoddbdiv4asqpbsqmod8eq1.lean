import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Parity
import Mathlib.Tactic


theorem numbertheory_aoddbdiv4asqpbsqmod8eq1
    (a b : ℤ) (ha : Int.Odd a) (hb : 4 ∣ b) :
    (a^2 + b^2) ≡ 1 [ZMOD 8] := by
  
  rcases ha with ⟨m, hm⟩
  rcases hb with ⟨k, hk⟩
  
  have h1 : ((2 * m + 1 : ℤ)^2) ≡ 1 [ZMOD 8] := by
    change (8 : ℤ) ∣ ((2 * m + 1)^2 - 1)
    
    have : ((2 * m + 1 : ℤ)^2 - 1) = 4 * m * (m + 1) := by
      ring
    
    have h2 : (2 : ℤ) ∣ m * (m + 1) := by
      rcases Int.even_or_odd m with hm_even | hm_odd
      · have : (2 : ℤ) ∣ m := hm_even.dvd
        exact dvd_mul_of_dvd_left this (m + 1)
      · have : (2 : ℤ) ∣ (m + 1) := (Int.Odd.add_one hm_odd).dvd
        exact dvd_mul_of_dvd_right this m
    rcases h2 with ⟨t, ht⟩
    
    refine ⟨t, ?_⟩
    calc
      4 * m * (m + 1)
          = 4 * (m * (m + 1)) := by ring
      _ = 4 * (2 * t) := by simpa [ht]
      _ = 8 * t := by ring
    
    · simpa [this]
  
  have h2 : ((4 * k : ℤ)^2) ≡ 0 [ZMOD 8] := by
    change (8 : ℤ) ∣ ((4 * k)^2 - 0)
    refine ⟨2 * k^2, ?_⟩
    ring
  
  have hsum := h1.add h2
  
  simpa [hm, hk] using hsum
