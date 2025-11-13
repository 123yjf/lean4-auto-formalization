import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic


 theorem mathd_numbertheory_521
   (small large : ℕ) (hs_pos : 0 < small) (hl_pos : 0 < large)
   (hs_even : Even small) (hl_even : Even large)
   (hconsec : large = small + 2) (hprod : small * large = 288) : large = 18 := by
  
  rcases hs_even with ⟨x, rfl⟩
  rcases hl_even with ⟨y, rfl⟩
  
  have hyx : y = x + 1 := by
    have : 2 * y = 2 * (x + 1) := by
      simpa [Nat.mul_add, two_mul, one_mul, add_comm, add_left_comm, add_assoc] using hconsec
    exact Nat.mul_right_cancel (by decide : 0 < 2) this
  subst hyx
  
  have h4 : 4 * (x * (x + 1)) = 288 := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, two_mul, one_mul, Nat.mul_add] using hprod
  have hxy : x * (x + 1) = 72 := by
    have : 4 * (x * (x + 1)) = 4 * 72 := by
      simpa using h4.trans (by decide : 288 = 4 * 72)
    exact Nat.mul_left_cancel (by decide : 0 < 4) this
  
  have hxZ : (x : ℤ) * (x + 1) = 72 := by exact_mod_cast hxy
  have hquad : (x : ℤ)^2 + (x : ℤ) - 72 = 0 := by
    have : (x : ℤ)^2 + (x : ℤ) = 72 := by
      simpa [pow_two, mul_add, add_comm, add_left_comm, add_assoc, one_mul] using hxZ
    simpa [sub_eq_add_neg, this]
  have hfac : ((x : ℤ) - 8) * ((x : ℤ) + 9) = 0 := by
    have : ((x : ℤ) - 8) * ((x : ℤ) + 9) = (x : ℤ)^2 + (x : ℤ) - 72 := by ring
    simpa [this] using hquad
  have hx8 : x = 8 := by
    rcases mul_eq_zero.mp hfac with h1 | h2
    · have : (x : ℤ) = 8 := by simpa using sub_eq_zero.mp h1
      exact Int.ofNat.inj this
    · have : (x : ℤ) + 9 ≠ 0 :=
        ne_of_gt (add_pos_of_nonneg_of_pos (Int.ofNat_nonneg x) (by decide : (0 : ℤ) < 9))
      exact (this h2).elim
  
  simpa [hx8]
