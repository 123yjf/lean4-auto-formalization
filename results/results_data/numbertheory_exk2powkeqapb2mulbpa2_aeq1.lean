import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


lemma numbertheory_exk2powkeqapb2mulbpa2_k1_impossible
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : (a + b^2) * (b + a^2) = 2) : False := by
  have ha1 : 1 ≤ a := Nat.succ_le_of_lt ha
  have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
  have hb2 : 1 ≤ b^2 := by
    
    simpa [pow_two] using Nat.mul_le_mul hb1 hb1
  have ha2sq : 1 ≤ a^2 := by
    
    simpa [pow_two] using Nat.mul_le_mul ha1 ha1
  have hA : 2 ≤ a + b^2 := by
    have : 1 + 1 ≤ a + b^2 := by exact add_le_add ha1 hb2
    simpa using this
  have hB : 2 ≤ b + a^2 := by
    have : 1 + 1 ≤ b + a^2 := by exact add_le_add hb1 ha2sq
    simpa using this
  have hge : 4 ≤ (a + b^2) * (b + a^2) := Nat.mul_le_mul hA hB
  have : (4 : ℕ) ≤ 2 := by simpa [h] using hge
  exact (by decide : ¬ (4 ≤ 2)) this



lemma factors_are_pow2
    {a b k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h : (a + b^2) * (b + a^2) = 2^k) :
    ∃ r s : ℕ, a + b^2 = 2^r ∧ b + a^2 = 2^s := by
  have hApos : 2 ≤ a + b^2 := by
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt ha
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
    have hb2 : 1 ≤ b^2 := by simpa [pow_two] using Nat.mul_le_mul hb1 hb1
    have : 1 + 1 ≤ a + b^2 := add_le_add ha1 hb2
    simpa using this
  have hBpos : 2 ≤ b + a^2 := by
    have ha1 : 1 ≤ a := Nat.succ_le_of_lt ha
    have hb1 : 1 ≤ b := Nat.succ_le_of_lt hb
    have ha2 : 1 ≤ a^2 := by simpa [pow_two] using Nat.mul_le_mul ha1 ha1
    have : 1 + 1 ≤ b + a^2 := add_le_add hb1 ha2
    simpa using this
  have hA_dvd : a + b^2 ∣ 2^k := by exact ⟨b + a^2, by simpa [Nat.mul_comm] using h.symm⟩
  have hB_dvd : b + a^2 ∣ 2^k := by exact ⟨a + b^2, by simpa [Nat.mul_comm] using h.symm⟩
  
  obtain ⟨r, hrle, hr⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hA_dvd
  obtain ⟨s, hsle, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hB_dvd
  
  exact ⟨r, s, hr, hs⟩
































