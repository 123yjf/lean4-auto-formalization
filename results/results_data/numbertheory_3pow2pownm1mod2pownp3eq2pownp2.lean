import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Multiplicity
import Mathlib.Tactic


theorem numbertheory_3pow2pownm1mod2pownp3eq2pownp2
    (n : ℕ) (hn : 0 < n) :
    ((3 : ZMod (2^(n+3))) ^ (2^n) - 1) = (2^(n+2) : ZMod (2^(n+3))) := by
  
  have h_even : Even (2^n) := by
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨k, hk⟩
    refine ⟨2^k, ?_⟩
    simp [hk, pow_succ, Nat.mul_comm]
  have hne0 : (2^n) ≠ 0 := by exact pow_ne_zero n (by decide : (2 : ℕ) ≠ 0)
  have hLTE : padicValNat 2 (3^(2^n) - 1) + 1
      = padicValNat 2 (3 + 1) + padicValNat 2 (3 - 1) + padicValNat 2 (2^n) := by
    simpa using
      (padicValNat.pow_two_sub_pow (hyx := by decide) (hxy := by decide)
        (hx := by decide) (hn := by exact hne0) (hneven := h_even))
  
  have _inst2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hv2_two : padicValNat 2 2 = 1 := by simpa using (padicValNat_self (p := 2))
  have hv2_four : padicValNat 2 4 = 2 := by
    simpa [pow_two] using (padicValNat.prime_pow (p := 2) (n := 2))
  have hv2_pow : padicValNat 2 (2^n) = n := by
    simpa using (padicValNat.prime_pow (p := 2) (n := n))
  
  have hsucc : padicValNat 2 (3^(2^n) - 1) + 1 = n + 3 := by
    simpa [hv2_four, hv2_two, hv2_pow, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hLTE
  have hval : padicValNat 2 (3^(2^n) - 1) = n + 2 := by
    have : Nat.succ (padicValNat 2 (3^(2^n) - 1)) = Nat.succ (n + 2) := by
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsucc
    exact Nat.succ_injective this
  
  have hdiv : 2^(n+2) ∣ (3^(2^n) - 1) := by
    
    exact (padicValNat_dvd_iff (p := 2) (n := n+2) (a := 3^(2^n) - 1)).mpr
      (Or.inr (by simpa [hval]))
  obtain ⟨k, hk⟩ := hdiv
  
  have hk_ne0 : k ≠ 0 := by
    
    intro h
    subst h
    have : 3^(2^n) = 1 := by simpa [Nat.mul_zero] using hk
    
    have : (1 : ℕ) < 3^(2^n) := by
      have h2n_ge : 2 ≤ 2^n := by
        rcases Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hn) with ⟨t, ht⟩
        simpa [ht, pow_succ] using (Nat.le_mul_of_pos_left (Nat.succ_pos _) : 2 ≤ 2 * 2^t)
      exact lt_of_le_of_lt (pow_le_pow_of_le_left (by decide : 0 ≤ 3) h2n_ge) (by decide)
    exact (ne_of_lt this) (by simpa)
  have hv_mul : padicValNat 2 (2^(n+2) * k)
      = padicValNat 2 (2^(n+2)) + padicValNat 2 k := by
    have hpowne : 2^(n+2) ≠ 0 := by exact pow_ne_zero (n+2) (by decide : (2 : ℕ) ≠ 0)
    simpa using (padicValNat.mul (p := 2) (a := 2^(n+2)) (b := k) hpowne hk_ne0)
  have hv_k : padicValNat 2 k = 0 := by
    
    have hv_left : padicValNat 2 (2^(n+2) * k) = (n+2) + padicValNat 2 k := by
      simpa [Nat.add_comm] using hv_mul
    have : padicValNat 2 (3^(2^n) - 1) = (n+2) + padicValNat 2 k := by
      simpa [hk] using hv_left
    
    have : Nat.succ (padicValNat 2 (3^(2^n) - 1)) = Nat.succ ((n+2) + padicValNat 2 k) := by
      simpa [Nat.succ_eq_add_one] using congrArg (fun t => t + 1) this
    have : Nat.succ (n + 2) = Nat.succ ((n+2) + padicValNat 2 k) := by
      simpa [hval]
    exact Nat.succ_injective (by
      simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this)
  have k_odd : Nat.Odd k := by
    
    refine Nat.odd_iff_not_even.mpr ?_
    intro hk_even
    rcases hk_even with ⟨t, ht⟩
    have : 1 ≤ padicValNat 2 k :=
      one_le_padicValNat_of_dvd (p := 2) (n := k) (hn := hk_ne0) (by simpa [ht])
    simpa [this] using hv_k
  
  
  obtain ⟨s, hs⟩ := k_odd.exists_two_mul_add_one
  have : ((3^(2^n) - 1 : ℕ) : ZMod (2^(n+3)))
      = (2^(n+2) : ZMod (2^(n+3))) * (k : ZMod (2^(n+3))) := by
    simpa [hk, Nat.cast_mul] using (rfl : ((3^(2^n) - 1 : ℕ) : ZMod (2^(n+3)))
      = (3^(2^n) - 1 : ℕ))
  
  calc
    ((3 : ZMod (2^(n+3))) ^ (2^n) - 1)
        = ((3^(2^n) - 1 : ℕ) : ZMod (2^(n+3))) := by
          
          
          norm_cast
    _ = (2^(n+2) : ZMod (2^(n+3))) * (k : ZMod (2^(n+3))) := by simpa using this
    _ = (2^(n+2) : ZMod (2^(n+3))) * ((2 * s + 1 : ℕ) : ZMod (2^(n+3))) := by
          simpa [hs]
    _ = (2^(n+2) : ZMod (2^(n+3))) * (1 : ZMod (2^(n+3)))
          + (2^(n+2) : ZMod (2^(n+3))) * ((2 * s : ℕ) : ZMod (2^(n+3))) := by
          ring
    _ = (2^(n+2) : ZMod (2^(n+3))) + (2^(n+3) : ZMod (2^(n+3))) * (s : ZMod (2^(n+3))) := by
          simp [Nat.cast_mul, pow_succ, two_mul, Nat.cast_add, Nat.cast_one, Nat.cast_bit0,
            Nat.cast_ofNat, mul_add, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc]
    _ = (2^(n+2) : ZMod (2^(n+3))) := by simp
