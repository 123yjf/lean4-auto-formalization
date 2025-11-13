import Mathlib.Data.Real.Irrational
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic


theorem exists_irrational_power_rational : ∃ (a b : ℝ), Irrational a ∧ Irrational b ∧ ∃ (q : ℚ), a^b = q := by
  
  
  have h_sqrt2_irr : Irrational (Real.sqrt 2) := by
    exact irrational_sqrt_two

  
  by_cases h : ∃ (q : ℚ), (Real.sqrt 2)^(Real.sqrt 2) = q

  
  case pos =>
    obtain ⟨q, hq⟩ := h
    use Real.sqrt 2, Real.sqrt 2
    constructor
    · exact h_sqrt2_irr
    constructor
    · exact h_sqrt2_irr
    · exact ⟨q, hq⟩

  
  case neg =>
    
    have h_sqrt2_pow_sqrt2_irr : Irrational ((Real.sqrt 2)^(Real.sqrt 2)) := by
      intro ⟨q, hq⟩
      exact h ⟨q, hq.symm⟩

    
    use (Real.sqrt 2)^(Real.sqrt 2), Real.sqrt 2
    constructor
    · exact h_sqrt2_pow_sqrt2_irr
    constructor
    · exact h_sqrt2_irr
    · 
      use 2
      have h_sqrt2_pos : 0 < Real.sqrt 2 := by
        exact Real.sqrt_pos.mpr (by norm_num)
      have h_sqrt2_nonneg : 0 ≤ Real.sqrt 2 := h_sqrt2_pos.le
      have : ((Real.sqrt 2)^(Real.sqrt 2))^(Real.sqrt 2) = (Real.sqrt 2)^((Real.sqrt 2) * (Real.sqrt 2)) := by
        exact (Real.rpow_mul h_sqrt2_nonneg (Real.sqrt 2) (Real.sqrt 2)).symm
      rw [this]
      have : (Real.sqrt 2) * (Real.sqrt 2) = 2 := by
        exact Real.mul_self_sqrt (by norm_num)
      rw [this]
      have : (Real.sqrt 2)^(2 : ℝ) = 2 := by
        rw [Real.rpow_two]
        exact Real.sq_sqrt (by norm_num)
      exact this



