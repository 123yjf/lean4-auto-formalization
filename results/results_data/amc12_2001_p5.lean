



import Mathlib

open scoped BigOperators
open Finset

namespace AMC12_2001_P5


lemma prodOdds_mul_pow_two_mul_factorial (n : ℕ) :
    (∏ k ∈ range n, (2 * k + 1)) * (2 ^ n) * Nat.factorial n = Nat.factorial (2 * n) := by
  induction' n with n ih
  · 
    simp
  · 
    
    calc
      (∏ k ∈ range (n + 1), (2 * k + 1)) * 2 ^ (n + 1) * Nat.factorial (n + 1)
          = ((∏ k ∈ range n, (2 * k + 1)) * (2 * n + 1)) * (2 ^ n * 2) * ((n + 1) * Nat.factorial n) := by
            simp [range_succ, pow_succ, Nat.factorial_succ, mul_comm, mul_left_comm, mul_assoc]
      _ = ((∏ k ∈ range n, (2 * k + 1)) * 2 ^ n * Nat.factorial n) * ((2 * n + 1) * 2 * (n + 1)) := by
            simp [mul_comm, mul_left_comm, mul_assoc]
      _ = Nat.factorial (2 * n) * ((2 * n + 1) * 2 * (n + 1)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              congrArg (fun x => x * ((2 * n + 1) * 2 * (n + 1))) ih
      _ = Nat.factorial (2 * (n + 1)) := by
        
        have htwo : 2 * (n + 1) = 2 * n + 2 := by
          simp [Nat.mul_add, two_mul, mul_one, add_comm, add_left_comm, add_assoc]
        
        have h1 : Nat.factorial (2 * n + 2) = (2 * n + 2) * Nat.factorial (2 * n + 1) := by
          simpa using Nat.factorial_succ (2 * n + 1)
        have h2 : Nat.factorial (2 * n + 1) = (2 * n + 1) * Nat.factorial (2 * n) := by
          simpa using Nat.factorial_succ (2 * n)
        
        have hfac' : (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n) = Nat.factorial (2 * (n + 1)) := by
          calc
            (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n)
                = (2 * n + 2) * ((2 * n + 1) * Nat.factorial (2 * n)) := by
                  simp [mul_comm, mul_left_comm, mul_assoc]
            _ = (2 * n + 2) * Nat.factorial (2 * n + 1) := by
                  simpa [h2]
            _ = Nat.factorial (2 * n + 2) := by
                  simpa using h1
            _ = Nat.factorial (2 * (n + 1)) := by
                  simpa [htwo, mul_comm]
        calc
          Nat.factorial (2 * n) * ((2 * n + 1) * 2 * (n + 1))
              = Nat.factorial (2 * n) * ((2 * n + 1) * (2 * (n + 1))) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
          _ = Nat.factorial (2 * n) * ((2 * n + 1) * (2 * n + 2)) := by
                simp [htwo]
          _ = (2 * n + 2) * (2 * n + 1) * Nat.factorial (2 * n) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
          _ = Nat.factorial (2 * (n + 1)) := by
                simpa [mul_comm, mul_left_comm, mul_assoc] using hfac'


def P : ℚ := ∏ k ∈ range 5000, ((2 * k + 1 : ℚ))


theorem amc12_2001_p5 :
    P = (Nat.factorial 10000 : ℚ) / ((2 : ℚ) ^ 5000 * (Nat.factorial 5000 : ℚ)) := by
  
  have hℕ := prodOdds_mul_pow_two_mul_factorial 5000
  have hℚ :
      (∏ k ∈ range 5000, ((2 * k + 1 : ℚ))) * (2 : ℚ) ^ 5000 * (Nat.factorial 5000 : ℚ)
        = (Nat.factorial 10000 : ℚ) := by
    
    exact_mod_cast hℕ
  have hden_ne : ((2 : ℚ) ^ 5000 * (Nat.factorial 5000 : ℚ)) ≠ 0 := by
    have h1 : (2 : ℚ) ^ 5000 ≠ 0 := pow_ne_zero _ (by norm_num)
    have h2 : (Nat.factorial 5000 : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.factorial_ne_zero 5000)
    exact mul_ne_zero h1 h2
  
  
  let a : ℚ := ∏ k ∈ range 5000, ((2 * k + 1 : ℚ))
  let b : ℚ := (2 : ℚ) ^ 5000
  let c : ℚ := (Nat.factorial 5000 : ℚ)
  have hm : a * (b * c) = (Nat.factorial 10000 : ℚ) := by
    have htmp := hℚ
    exact (mul_assoc a b c).symm.trans htmp
  exact (eq_div_iff_mul_eq hden_ne).2 hm

end AMC12_2001_P5
