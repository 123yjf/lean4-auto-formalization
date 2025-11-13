import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Tactic



theorem mathd_numbertheory_582 (n : ℤ) (h : n ≡ 0 [ZMOD 3]) :
  (n + 4) + (n + 6) + (n + 8) ≡ 0 [ZMOD 9] := by
  
  rw [Int.ModEq] at h ⊢
  
  have h1 : (n + 4) + (n + 6) + (n + 8) = 3 * n + 18 := by ring
  rw [h1]
  
  obtain ⟨k, hk⟩ := Int.dvd_iff_emod_eq_zero.mpr h
  rw [hk]
  
  ring_nf
  
  
  rw [mul_comm k 9]
  
  have h2 : 18 + 9 * k = 9 * (2 + k) := by ring
  rw [h2]
  
  simp [Int.mul_emod]
