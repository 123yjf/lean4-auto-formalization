import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases





def primes_set : Finset ℕ := {5, 7, 11, 13, 17}


def prime_diff (p q : ℕ) : ℕ := p * q - (p + q)


lemma achievable_119 : prime_diff 11 13 = 119 := by
  unfold prime_diff
  norm_num


lemma options_mod_4 :
  (22 : ℕ) ≡ 2 [MOD 4] ∧
  (60 : ℕ) ≡ 0 [MOD 4] ∧
  (119 : ℕ) ≡ 3 [MOD 4] ∧
  (180 : ℕ) ≡ 0 [MOD 4] ∧
  (231 : ℕ) ≡ 3 [MOD 4] := by
  simp [Nat.ModEq]


theorem amc12_2000_p6_simplified :
  ∃ p ∈ primes_set, ∃ q ∈ primes_set, p ≠ q ∧ prime_diff p q = 119 := by
  use 11, by simp [primes_set], 13, by simp [primes_set]
  constructor
  · norm_num
  · exact achievable_119


lemma algebraic_identity_specific :
  prime_diff 11 13 = (11 - 1) * (13 - 1) - 1 := by
  unfold prime_diff
  norm_num


lemma congruence_mod_4_specific :
  prime_diff 11 13 ≡ 3 [MOD 4] := by
  unfold prime_diff
  
  
  simp [Nat.ModEq]


lemma upper_bound_specific : prime_diff 13 17 = 191 := by
  unfold prime_diff
  norm_num
