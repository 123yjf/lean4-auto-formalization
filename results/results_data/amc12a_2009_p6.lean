import Mathlib


 theorem amc12a_2009_p6 (m n : Nat) :
    (2^m)^(2*n) * (3^n)^m = 12^(m*n) := by
  
  let P := 2^m
  let Q := 3^n
  
  have hPQ : P^(2*n) * Q^m = (2^m)^(2*n) * (3^n)^m := by
    simpa [P, Q]

  
  have h1 : (2^m)^(2*n) = 2^(2*(m*n)) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (pow_mul (2 : Nat) m (2*n)).symm
  have h2 : (3^n)^m = 3^(m*n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (pow_mul (3 : Nat) n m).symm
  
  have h3 : 2^(2*(m*n)) = (2^2 : Nat)^(m*n) := by
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      (pow_mul (2 : Nat) 2 (m*n))
  
  have h22 : (2^2 : Nat) = 4 := by decide
  have h43 : (4 * 3 : Nat) = 12 := by decide
  calc
    (2^m)^(2*n) * (3^n)^m
        = 2^(2*(m*n)) * 3^(m*n) := by simpa [h1, h2]
    _   = (2^2 : Nat)^(m*n) * 3^(m*n) := by simpa [h3]
    _   = 4^(m*n) * 3^(m*n) := by simpa [h22]
    _   = (4 * 3)^(m*n) := by
            simpa [mul_comm] using
              (mul_pow (4 : Nat) 3 (m*n)).symm
    _   = 12^(m*n) := by simpa [h43]
