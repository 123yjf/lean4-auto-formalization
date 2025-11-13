import Mathlib/NumberTheory/Mersenne


 theorem numbertheory_2pownm1prime_nprime
     (n : ℕ) (hp : Nat.Prime (2^n - 1)) : Nat.Prime n := by
   have h' : Nat.Prime (Nat.mersenne n) := by simpa [Nat.mersenne] using hp
   simpa using Nat.prime_of_mersenne_prime h'
