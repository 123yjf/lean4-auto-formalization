import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring



theorem imo_2019_p1 : ∀ f : ℤ → ℤ,
  (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) ↔
  ((∀ x, f x = 0) ∨ ∃ c : ℤ, ∀ x, f x = 2 * x + c) := by
  intro f
  constructor
  · 
    intro h
    
    have eq1 : ∀ b : ℤ, f 0 + 2 * f b = f (f b) := by
      intro b
      have := h 0 b
      simp at this
      exact this
    have eq2 : ∀ a : ℤ, f (2 * a) + 2 * f 0 = f (f a) := by
      intro a
      have := h a 0
      simp at this
      exact this
    have eq3 : ∀ a : ℤ, f (2 * a) = 2 * f a - f 0 := by
      intro a
      have h1 := eq1 a
      have h2 := eq2 a
      
      
      
      have : f 0 + 2 * f a = f (2 * a) + 2 * f 0 := by
        rw [h1, ← h2]
      linarith

    
    have eq4 : ∀ a b : ℤ, f (a + b) = f a + f b - f 0 := by
      intro a b
      have orig := h a b
      have h1 := eq1 b
      have h3 := eq3 a
      
      
      
      
      
      have h_target := eq1 (a + b)
      rw [h3] at orig
      rw [← h_target] at orig
      linarith

    
    let g := fun x => f x - f 0
    have cauchy : ∀ a b : ℤ, g (a + b) = g a + g b := by
      intro a b
      simp [g]
      have := eq4 a b
      linarith
    have linear : ∃ d : ℤ, g = fun x => d * x := by
      
      use g 1
      funext x
      
      rw [mul_comm]
      
      induction x using Int.induction_on with
      | hz => 
        simp [g]
      | hp n ih => 
        rw [cauchy, ih]
        rw [add_mul, one_mul]
      | hn n ih => 
        have h_rewrite : -(↑n : ℤ) - 1 = (-(↑n : ℤ)) + (-1) := by ring
        rw [h_rewrite, cauchy, ih]
        have g_neg_one : g (-1) = -g 1 := by
          have : g 0 = g (1 + (-1)) := by ring
          rw [cauchy] at this
          have g_zero : g 0 = 0 := by simp [g]
          rw [g_zero] at this
          linarith
        rw [g_neg_one]
        ring

    
    obtain ⟨d, hd⟩ := linear
    have constraint1 : d * (d - 2) = 0 := by
      
      have f_form : ∀ x, f x = d * x + f 0 := by
        intro x
        have : f x = g x + f 0 := by simp [g]
        rw [this, hd]
      
      have h1 := h 1 0
      simp at h1
      rw [f_form, f_form, f_form] at h1
      
      have h2 := h 0 0
      simp at h2
      rw [f_form] at h2
      
      
      
      have h_eq : d * (d - 2) = 0 := by
        
        
        
        
        
        
        
        
        
        
        
        
        have h1_simp : 2 * d + 3 * f 0 = f (f 1) := by
          have h_expand : d * 2 + f 0 + 2 * f 0 = 2 * d + 3 * f 0 := by ring
          rw [← h_expand]
          simp at h1
          exact h1
        have h2_simp : 3 * f 0 = f (f 0) := by
          have h_expand : f 0 + 2 * f 0 = 3 * f 0 := by ring
          rw [← h_expand]
          simp at h2
          exact h2
        have h_f1 : f 1 = d + f 0 := by
          have h_form := f_form 1
          simp at h_form
          exact h_form
        have h_ff1 : f (f 1) = d ^ 2 + d * f 0 + f 0 := by
          rw [h_f1, f_form]
          ring
        have h_ff0 : f (f 0) = d * f 0 + f 0 := f_form (f 0)
        rw [h_ff1] at h1_simp
        rw [h_ff0] at h2_simp
        
        
        have h_from_h2 : 2 * f 0 = d * f 0 := by
          have h_rearrange : 3 * f 0 - f 0 = d * f 0 + f 0 - f 0 := by rw [h2_simp]
          have h_left : 3 * f 0 - f 0 = 2 * f 0 := by ring
          have h_right : d * f 0 + f 0 - f 0 = d * f 0 := by ring
          rw [h_left, h_right] at h_rearrange
          exact h_rearrange
        have h_substitute : 2 * d + 3 * f 0 = d ^ 2 + 2 * f 0 + f 0 := by
          rw [← h_from_h2] at h1_simp
          exact h1_simp
        have h_simplify : 2 * d + 3 * f 0 = d ^ 2 + 3 * f 0 := by
          
          
          
          have h_combine : d ^ 2 + 2 * f 0 + f 0 = d ^ 2 + 3 * f 0 := by ring
          rw [← h_combine]
          exact h_substitute
        have h_cancel : 2 * d = d ^ 2 := by
          have h_sub : 2 * d + 3 * f 0 - 3 * f 0 = d ^ 2 + 3 * f 0 - 3 * f 0 := by rw [h_simplify]
          have h_left : 2 * d + 3 * f 0 - 3 * f 0 = 2 * d := by ring
          have h_right : d ^ 2 + 3 * f 0 - 3 * f 0 = d ^ 2 := by ring
          rw [h_left, h_right] at h_sub
          exact h_sub
        have h_rearrange : d ^ 2 - 2 * d = 0 := by
          rw [← h_cancel]
          ring
        have h_factor : d * (d - 2) = d ^ 2 - 2 * d := by ring
        rw [h_factor]
        exact h_rearrange
      exact h_eq
    have constraint2 : (d - 2) * f 0 = 0 := by
      
      have f_form : ∀ x, f x = d * x + f 0 := by
        intro x
        have : f x = g x + f 0 := by simp [g]
        rw [this, hd]
      
      have h2 := h 0 0
      simp at h2
      rw [f_form] at h2
      
      have h_eq : (d - 2) * f 0 = 0 := by
        
        
        
        
        have h_orig : f 0 + 2 * f 0 = f (f 0) := by
          have := h 0 0
          simp at this
          exact this
        rw [f_form] at h_orig
        simp at h_orig
        
        
        
        have h_eq_form : 3 * f 0 = d * f 0 + f 0 := by
          have h_left : f 0 + 2 * f 0 = 3 * f 0 := by ring
          have h_right : f (f 0) = d * f 0 + f 0 := f_form (f 0)
          rw [← h_left, ← h_right]
          exact h_orig
        have h_subtract : 2 * f 0 = d * f 0 := by
          
          have h_rearrange : 3 * f 0 - f 0 = d * f 0 + f 0 - f 0 := by
            rw [h_eq_form]
          have h_left : 3 * f 0 - f 0 = 2 * f 0 := by ring
          have h_right : d * f 0 + f 0 - f 0 = d * f 0 := by ring
          rw [h_left, h_right] at h_rearrange
          exact h_rearrange
        have h_factor : f 0 * (2 - d) = 0 := by
          have h_expand : 2 * f 0 - d * f 0 = 0 := by
            rw [← h_subtract]
            ring
          have h_factor_eq : f 0 * (2 - d) = 2 * f 0 - d * f 0 := by ring
          rw [h_factor_eq]
          exact h_expand
        have h_sign : (d - 2) * f 0 = -(f 0 * (2 - d)) := by ring
        rw [h_sign, h_factor]
        simp
      exact h_eq

    
    have h_cases : d = 0 ∨ d = 2 := by
      rw [mul_eq_zero] at constraint1
      cases constraint1 with
      | inl h1 => left; exact h1
      | inr h2 =>
        right
        have h_d_eq_2 : d = 2 := by
          have h_add : d - 2 + 2 = 0 + 2 := by rw [h2]
          simp at h_add
          exact h_add
        exact h_d_eq_2
    cases h_cases with
    | inl h_d_zero =>
      
      left
      
      
      
      intro x
      have h_g_zero : g x = 0 := by
        rw [hd, h_d_zero]
        simp
      simp [g] at h_g_zero
      have h_f0_zero : f 0 = 0 := by
        rw [h_d_zero] at constraint2
        simp at constraint2
        exact constraint2
      rw [h_f0_zero] at h_g_zero
      simp at h_g_zero
      exact h_g_zero
    | inr h_d_two =>
      
      right
      use f 0
      
      intro x
      have h_g_form : g x = 2 * x := by
        rw [hd, h_d_two]
      simp [g] at h_g_form
      have h_result : f x = 2 * x + f 0 := by
        rw [← h_g_form]
        simp [g]
      exact h_result

  · 
    intro h
    cases' h with h1 h2
    · 
      intro a b
      rw [h1, h1, h1]
      simp
    · 
      obtain ⟨c, hc⟩ := h2
      intro a b
      rw [hc, hc, hc]
      
      
      ring_nf
      rw [hc]
      ring_nf
