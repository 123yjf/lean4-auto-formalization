import Mathlib.Tactic


namespace MathdAlgebra113


noncomputable def f (x : ℝ) : ℝ := x^2 - 14 * x + 3


 theorem mathd_algebra_113 :
  (∀ x : ℝ, f x ≥ f 7) ∧ (∀ x : ℝ, f x = f 7 → x = 7) := by
  
  have hsq : ∀ x : ℝ, f x = (x - 7)^2 - 46 := by
    intro x
    dsimp [f]
    ring
  
  have h7 : f 7 = -46 := by simpa [hsq 7]
  constructor
  · 
    intro x
    have : -46 ≤ (x - 7)^2 - 46 := by
      have hx : 0 ≤ (x - 7)^2 := by simpa using sq_nonneg (x - 7)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        add_le_add_right hx (-46)
    simpa [hsq x, h7] using this
  · 
    intro x hx
    
    have h0 : (x - 7)^2 - 46 = -46 := by simpa [hsq x, h7] using hx
    have hsq0 : (x - 7)^2 = 0 := by
      have := congrArg (fun t : ℝ => t + 46) h0
      simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this
    have hxminus : x - 7 = 0 := (sq_eq_zero_iff.mp hsq0)
    exact (sub_eq_zero.mp hxminus)

end MathdAlgebra113
