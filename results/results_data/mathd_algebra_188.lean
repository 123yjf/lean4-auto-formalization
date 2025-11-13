import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Equiv.Defs


theorem mathd_algebra_188 [Nonempty ℕ] (f : ℕ → ℕ) (hf_bij : Function.Bijective f)
  (h1 : f 2 = 4) (h2 : Function.invFun f 2 = 4) : f (f 2) = 2 := by
  
  have h_f_4_eq_2 : f 4 = 2 := by
    
    have h_surj : Function.Surjective f := hf_bij.2
    have h_exists : ∃ a, f a = 2 := h_surj 2
    have h_inv_eq : f (Function.invFun f 2) = 2 := Function.invFun_eq h_exists
    rw [h2] at h_inv_eq
    exact h_inv_eq
  
  have h_f_f_2_eq_f_4 : f (f 2) = f 4 := by
    rw [h1]
  
  rw [h_f_f_2_eq_f_4, h_f_4_eq_2]
