import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

set_option maxRecDepth 100000

open scoped BigOperators


def hasExactlyFourDivisors (m : ℕ) : Prop :=
  ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≠ q ∧ m = p * q


def nice (n : ℕ) : Prop :=
  ∃ m, hasExactlyFourDivisors m ∧ (∑ d ∈ Nat.divisors m, d) = n


lemma mathd_numbertheory_451_exists : nice 2016 := by
  classical
  refine ⟨7 * 251, ?_, ?_⟩
  
  have hprime7  : Nat.Prime 7   := by decide
  have hprime251: Nat.Prime 251 := by decide
  have hneq : (7 : ℕ) ≠ 251 := by decide
  refine ⟨7, 251, hprime7, hprime251, hneq, rfl⟩
  
  have hcop : Nat.Coprime 7 251 := by decide
  have hsum_mul : (∑ d ∈ Nat.divisors (7 * 251), d)
      = (∑ d ∈ Nat.divisors 7, d) * (∑ d ∈ Nat.divisors 251, d) :=
    Nat.Coprime.sum_divisors_mul (m:=7) (n:=251) hcop
  
  have hsum7   : (∑ d ∈ Nat.divisors 7, d) = 1 + 7 := by
    simpa [ArithmeticFunction.sigma_one_apply, Finset.range_succ, Nat.pow_zero, Nat.pow_one]
      using (ArithmeticFunction.sigma_one_apply_prime_pow (p:=7) (i:=1) (by decide))
  have hsum251 : (∑ d ∈ Nat.divisors 251, d) = 1 + 251 := by
    simpa [ArithmeticFunction.sigma_one_apply, Finset.range_succ, Nat.pow_zero, Nat.pow_one]
      using (ArithmeticFunction.sigma_one_apply_prime_pow (p:=251) (i:=1) (by decide))
  
  simpa [hsum_mul, hsum7, hsum251, Nat.mul_add, Nat.add_mul]


theorem mathd_numbertheory_451_at_least_one :
  (∃ n, 2010 ≤ n ∧ n ≤ 2019 ∧ nice n) := by
  refine ⟨2016, by decide, by decide, mathd_numbertheory_451_exists⟩
