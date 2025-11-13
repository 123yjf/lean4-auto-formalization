import Mathlib

open Finset
open BigOperators


lemma two_mul_sum_range_add (n : ℕ) :
    2 * (∑ i ∈ range n, i) + n = n^2 := by
  induction' n with n ih
  · simp
  · 
    have hsum : (∑ i ∈ range (n + 1), i) = (∑ i ∈ range n, i) + n := by
      simpa [range_succ] using sum_range_succ (fun i => i) n
    
    calc
      2 * (∑ i ∈ range (n + 1), i) + (n + 1)
          = 2 * ((∑ i ∈ range n, i) + n) + (n + 1) := by
            simpa [hsum]
      _ = (2 * (∑ i ∈ range n, i) + n) + (2 * n + 1) := by
        simp [two_mul, mul_add, add_comm, add_left_comm, add_assoc]
      _ = n^2 + (2 * n + 1) := by
        simpa [ih]
      _ = (n + 1)^2 := by
        simp [pow_two, two_mul, mul_add, add_comm, add_left_comm, add_assoc, Nat.mul_comm]


theorem sum_range_cube_eq_square_sum (n : ℕ) :
    (∑ i ∈ range n, i^3) = (∑ i ∈ range n, i)^2 := by
  induction' n with n ih
  · simp
  · 
    set S : ℕ := ∑ i ∈ range n, i
    
    have hsum : (∑ i ∈ range (n + 1), i) = S + n := by
      simpa [range_succ, S] using sum_range_succ (fun i => i) n
    have htri : 2 * S + n = n^2 := by
      simpa [S] using two_mul_sum_range_add n
    
    have hcubes : (∑ i ∈ range (n + 1), i^3) = (∑ i ∈ range n, i^3) + n^3 := by
      simpa [range_succ] using sum_range_succ (fun i => i^3) n
    
    have : (∑ i ∈ range n, i^3) + n^3 = (S + n)^2 := by
      
      
      have : (S + n)^2 = S^2 + (S * n + n * S) + n^2 := by
        
        simp [pow_two, add_mul, mul_add, add_comm, add_left_comm, add_assoc]
      
      have : (S + n)^2 = S^2 + 2 * (S * n) + n^2 := by
        simpa [pow_two, add_mul, mul_add, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
               two_mul, add_comm, add_left_comm, add_assoc] using this
      
      
      
      
      have hmul : n * (2 * S + n) = 2 * (S * n) + n^2 := by
        
        calc
          n * (2 * S + n) = n * (2 * S) + n * n := by
            simpa [mul_add]
          _ = 2 * (S * n) + n^2 := by
            simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, two_mul, pow_two, mul_add]
      
      have hpow3 : n^3 = n * (2 * S + n) := by
        
        simpa [pow_two, pow_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, htri]
          using congrArg (fun t => n * t) htri
      
      
      have h1 : (∑ i ∈ range n, i^3) + n^3 = (∑ i ∈ range n, i)^2 + n^3 := by
        exact congrArg (fun t => t + n^3) ih
      have h1' : (∑ i ∈ range n, i^3) + n^3 = S^2 + n^3 := by
        simpa [S] using h1
      
      have h2 : S^2 + n^3 = S^2 + n * (2 * S + n) := by
        simpa [hpow3]
      have h3 : S^2 + n * (2 * S + n) = S^2 + (2 * (S * n) + n^2) := by
        simpa [hmul]
      have h4 : S^2 + (2 * (S * n) + n^2) = S^2 + 2 * (S * n) + n^2 := by
        simp [add_assoc]
      have h5 : S^2 + 2 * (S * n) + n^2 = (S + n)^2 := by
        simpa [this]
      exact h1'.trans (h2.trans (h3.trans (h4.trans h5)))
    
    simpa [hcubes, hsum, S, add_comm, add_left_comm, add_assoc] using this
