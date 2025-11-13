import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Ring



theorem imo_1959_p1 (n : ℕ) : Nat.gcd (21 * n + 4) (14 * n + 3) = 1 := by
  
  rw [Nat.coprime_iff_gcd_eq_one.symm]
  
  
  rw [← Nat.isCoprime_iff_coprime]
  
  use (-2 : ℤ), (3 : ℤ)
  
  
  simp only [Int.natCast_add, Int.natCast_mul]
  ring
