import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Parity
import Mathlib.Tactic


 theorem mathd_numbertheory_430
   (A B C : ℕ)
   (hA1 : 1 ≤ A) (hA9 : A ≤ 9)
   (hB1 : 1 ≤ B) (hB9 : B ≤ 9)
   (hC1 : 1 ≤ C) (hC9 : C ≤ 9)
   (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C)
   (h1 : A + B = C)
   (h2 : 11 * A = 2 * C + B)
   (h3 : C * B = 11 * A + A) :
   A + B + C = 8 := by
  
  have h2' : 11 * A = 2 * (A + B) + B := by
    simpa [h1, two_mul, add_comm, add_left_comm, add_assoc] using h2
  have eq1 : 2 * A + 3 * B = 11 * A := by
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using h2'.symm
  have eq1' : 2 * A + 3 * B = 2 * A + 9 * A := by
    simpa [Nat.add_mul] using eq1.trans (by simpa using (by
      have : (2 + 9) * A = 11 * A := by simp
      exact this.symm))
  have hB3 : 3 * B = 9 * A := Nat.add_left_cancel eq1'
  have hB : B = 3 * A := by
    have : 3 * B = 3 * (3 * A) := by
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hB3
    exact Nat.mul_left_cancel (by decide : (3 : ℕ) ≠ 0) this
  
  have hC' : C = 4 * A := by
    have : C = A + 3 * A := by simpa [hB, add_comm, add_left_comm, add_assoc] using h1
    simpa [Nat.add_mul, one_mul] using this
  
  have hAA : A * A = A := by
    have : 12 * (A * A) = 12 * A := by
      simpa [hC', hB, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_mul, one_mul]
        using h3
    exact Nat.mul_left_cancel (by decide : (12 : ℕ) ≠ 0) this
  have hA_ne_zero : A ≠ 0 := by
    intro h; simpa [h] using hA1
  have hA1' : A = 1 := by
    have : A * A = 1 * A := by simpa [one_mul] using hAA
    exact Nat.mul_right_cancel hA_ne_zero this
  
  have hB' : B = 3 := by simpa [hA1'] using hB
  have hC'' : C = 4 := by simpa [hA1', hB'] using h1
  simpa [hA1', hB', hC'']
