import Mathlib

open Nat


def eulerP (n : ℕ) : ℕ := n * (n - 1) + 41

lemma eulerP_succ (n : ℕ) :
    eulerP (n+1) = eulerP n + 2*n := by
  
  cases' n with k
  · 
    simp [eulerP]
  · 
    
    simp [eulerP, Nat.succ_eq_add_one, Nat.add_mul, Nat.mul_add, two_mul,
          Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc, Nat.add_comm,
          Nat.add_left_comm, Nat.add_assoc]
    ring


lemma eulerP_41 : eulerP 41 = 41*41 := by
  
  have : 41*40 + 41 = 41*41 := by
    ring
  simpa [eulerP] using this

lemma eulerP_42 : eulerP 42 = 41*43 := by
  
  have : 42*41 + 41 = 41*43 := by
    ring
  simpa [eulerP, Nat.mul_comm] using this


lemma prime_dvd_gcd_eulerP (n : ℕ) (hn : 1 ≤ n)
  {q : ℕ} (hqprime : q.Prime)
  (hqgcd : q ∣ Nat.gcd (eulerP n) (eulerP (n+1))) : 41 ∣ n := by
  
  have hq₁ : q ∣ eulerP n := Nat.dvd_trans hqgcd (Nat.gcd_dvd_left _ _)
  have hq₂ : q ∣ eulerP (n+1) := Nat.dvd_trans hqgcd (Nat.gcd_dvd_right _ _)
  
  have hstep : eulerP (n+1) = eulerP n + 2*n := eulerP_succ n
  have hq₂n : q ∣ 2*n := by
    
    have hsum : q ∣ eulerP n + 2*n := by simpa [hstep] using hq₂
    exact (Nat.dvd_add_right hq₁).1 hsum
  
  have hodd_e : Odd (eulerP n) := by
    have heav : Even (n * (n-1)) := Nat.even_mul_pred_self n
    simpa [eulerP] using heav.add_odd (by decide : Odd (41 : ℕ))
  have hodd : ¬ (2 ∣ eulerP n) := by
    intro h2
    rcases h2 with ⟨k, hk⟩
    have : Even (eulerP n) := ⟨k, by simpa [two_mul] using hk⟩
    exact (odd_iff_not_even.mp hodd_e) this
  have hq_ne_two : q ≠ 2 := by
    intro hcontra
    subst hcontra
    exact hodd (by simpa using hq₁)
  
  have hq_dvd_n : q ∣ n := by
    rcases hqprime.dvd_mul.mp hq₂n with hq2 | hqn
    · have : q = 2 := by
        rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).1 hq2 with hq1 | hq2eq
        · exact (hqprime.ne_one hq1).elim
        · exact hq2eq
      exact (hq_ne_two this).elim
    · exact hqn
  
  
  rcases hq_dvd_n with ⟨k, hk⟩
  
  have hA : q ∣ eulerP (q*k) := by simpa [hk] using hq₁
  have hB : q ∣ q*k*(q*k - 1) := by
    have : q ∣ q*k := ⟨k, by simp⟩
    exact dvd_mul_of_dvd_left this (q*k - 1)
  have hq41 : q ∣ 41 := by
    have : q ∣ (q*k*(q*k - 1) + 41) := by
      simpa [eulerP, hk, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
             Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hA
    exact (Nat.dvd_add_left hB).1 this
  
  have h41prime : Nat.Prime 41 := by decide
  have hq_eq_41 : q = 41 := by
    rcases (Nat.dvd_prime h41prime).1 hq41 with hq1 | hq41'
    · exact (hqprime.ne_one hq1).elim
    · exact hq41'
  subst hq_eq_41
  exact hq_dvd_n


theorem mathd_numbertheory_618 :
  Nat.gcd (eulerP 41) (eulerP 42) = 41 ∧
  ∀ ⦃n : ℕ⦄, 0 < n → 1 < Nat.gcd (eulerP n) (eulerP (n+1)) → 41 ∣ n := by
  constructor
  · 
    have h1 : eulerP 41 = 41*41 := eulerP_41
    have h2 : eulerP 42 = 41*43 := eulerP_42
    
    have hgcd : Nat.gcd 41 43 = 1 := by decide
    have : Nat.gcd (41*41) (41*43) = 41 := by
      simpa [Nat.gcd_mul_left, hgcd]
    simpa [h1, h2] using this
  · intro n hnpos hg
    
    let q := Nat.minFac (Nat.gcd (eulerP n) (eulerP (n+1)))
    have hqprime : Nat.Prime q := by
      have : 1 < Nat.gcd (eulerP n) (eulerP (n+1)) := hg
      simpa [q] using Nat.minFac_prime this
    have hq : q ∣ Nat.gcd (eulerP n) (eulerP (n+1)) := by
      simpa [q] using Nat.minFac_dvd (Nat.gcd (eulerP n) (eulerP (n+1)))
    exact prime_dvd_gcd_eulerP n (Nat.succ_le_of_lt hnpos) hqprime hq
