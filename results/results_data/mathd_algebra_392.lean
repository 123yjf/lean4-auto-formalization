import Mathlib.Tactic


lemma sumsq_consecutive_evens (k : ℤ) :
    (2 * k - 2)^2 + (2 * k)^2 + (2 * k + 2)^2 = 12 * k^2 + 8 := by
  ring




lemma prod_div8_factor (k : \u2124) :
  (((2 * k - 2) * (2 * k) * (2 * k + 2) : \u2124) : \u211a) / 8
    = (k : \u211a) * (k - 1) * (k + 1) := by
  have hz : (2 * k - 2) * (2 * k) * (2 * k + 2) = 8 * k * (k - 1) * (k + 1) := by
    ring
  have hq : (((2 * k - 2) * (2 * k) * (2 * k + 2) : \u2124) : \u211a)
      = (8 : \u211a) * k * (k - 1) * (k + 1) := by
    exact_mod_cast hz
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hq

theorem mathd_algebra_392
    {a b c k : ℤ} (hk : 2 ≤ k)
    (ha : a = 2 * k - 2) (hb : b = 2 * k) (hc : c = 2 * k + 2)
    (hs : a^2 + b^2 + c^2 = 12296) :
    ((a * b * c : ℤ) : ℚ) / 8 = 32736 := by
  
  have hs' : 12 * k^2 + 8 = 12296 := by
    simpa [ha, hb, hc, sumsq_consecutive_evens] using hs
  have h1 : 12 * k^2 = 12288 := by linarith
  have h2 : 12 * k^2 = 12 * 1024 := by simpa using h1
  
  have hsq : k^2 = 1024 := by
    have h12 : (12 : ℤ) ≠ 0 := by decide
    exact mul_left_cancel₀ h12 h2
  
  have hk_nonneg : 0 ≤ k := le_trans (by norm_num) hk
  have hk32 : k = 32 := by
    have : k^2 = (32 : ℤ)^2 := by simpa [pow_two] using hsq
    have : k = 32 ∨ k = -32 := by
      simpa [pow_two] using (mul_self_eq_mul_self_iff.mp this)
    rcases this with hpos | hneg
    · exact hpos
    · exfalso
      have : 0 ≤ (-32 : ℤ) := by simpa [hneg] using hk_nonneg
      norm_num at this
  
  calc
    ((a * b * c : ℤ) : ℚ) / 8
        = (((2 * k - 2) * (2 * k) * (2 * k + 2) : ℤ) : ℚ) / 8 := by
          simpa [ha, hb, hc]
    _   = (k : ℚ) * (k - 1) * (k + 1) := by
          simpa using prod_div8_factor k
    _   = 32736 := by
          simpa [hk32] using (by norm_num : (32 : ℚ) * 31 * 33 = 32736)



theorem mathd_algebra_392_restated {k : ℤ} (hk : 2 ≤ k) :
  let a := 2 * k - 2; let b := 2 * k; let c := 2 * k + 2 →
  (a^2 + b^2 + c^2 = 12296) → ((a * b * c : ℤ) : ℚ) / 8 = 32736 := by
  intro hdef hs
  rcases hdef with rfl
  
  refine mathd_algebra_392 hk rfl rfl rfl ?_
  simpa



theorem mathd_algebra_392_pos {k : ℤ} (hk : 2 ≤ k) :
  let a := 2 * k - 2; let b := 2 * k; let c := 2 * k + 2 →
  (0 < a ∧ 0 < b ∧ 0 < c) →
  (a^2 + b^2 + c^2 = 12296) →
  ((a * b * c : ℤ) : ℚ) / 8 = 32736 := by
  intro _ _ hs
  simpa using (mathd_algebra_392 hk rfl rfl rfl hs)
