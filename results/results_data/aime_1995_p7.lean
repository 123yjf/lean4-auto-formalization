import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Order.Field.Basic

theorem aime_1995_p7 (t : ℝ) (h : (1 + Real.sin t) * (1 + Real.cos t) = 5/4) :
  ∃ (m n k : ℕ), Nat.gcd m n = 1 ∧
  (1 - Real.sin t) * (1 - Real.cos t) = m / n - Real.sqrt k ∧
  k + m + n = 27 := by
  
  let s := Real.sin t
  let c := Real.cos t
  have h1 : s + c + s * c = 1/4 := by
    have expand : (1 + s) * (1 + c) = 1 + s + c + s * c := by ring
    rw [expand] at h
    linarith

  
  let x := s + c
  have h2 : s * c = (x^2 - 1) / 2 := by
    have pythagorean : s^2 + c^2 = 1 := Real.sin_sq_add_cos_sq t
    have expand_x : x^2 = s^2 + 2*s*c + c^2 := by
      unfold x; ring
    have key : x^2 = 1 + 2*s*c := by
      rw [expand_x]; rw [← pythagorean]; ring
    linarith [key]

  
  have h3 : 2 * x^2 + 4 * x - 3 = 0 := by
    
    have eq1 : x + (x^2 - 1) / 2 = 1/4 := by rw [← h2]; exact h1
    
    have eq2 : 4*x + 2*(x^2 - 1) = 1 := by
      field_simp at eq1; linarith [eq1]
    
    linarith [eq2]

  
  have h4 : x = (-2 + Real.sqrt 10) / 2 := by
    
    
    have satisfies_quad : 2 * ((-2 + Real.sqrt 10) / 2)^2 + 4 * ((-2 + Real.sqrt 10) / 2) - 3 = 0 := by
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

    
    have sin_cos_bound : abs (Real.sin t + Real.cos t) ≤ Real.sqrt 2 := by
      have h_sq : (Real.sin t + Real.cos t)^2 ≤ 2 := by
        have expand : (Real.sin t + Real.cos t)^2 = (Real.sin t)^2 + 2 * Real.sin t * Real.cos t + (Real.cos t)^2 := by ring
        rw [expand]
        have bound_cross : 2 * Real.sin t * Real.cos t ≤ (Real.sin t)^2 + (Real.cos t)^2 := by
          have h_sq : 0 ≤ (Real.sin t - Real.cos t)^2 := sq_nonneg _
          have expand_sq : (Real.sin t - Real.cos t)^2 = (Real.sin t)^2 - 2 * Real.sin t * Real.cos t + (Real.cos t)^2 := by ring
          rw [expand_sq] at h_sq
          linarith [h_sq]
        calc (Real.sin t)^2 + 2 * Real.sin t * Real.cos t + (Real.cos t)^2
          _ ≤ (Real.sin t)^2 + ((Real.sin t)^2 + (Real.cos t)^2) + (Real.cos t)^2 := by
            linarith [bound_cross]
          _ = 2 * ((Real.sin t)^2 + (Real.cos t)^2) := by ring
          _ = 2 * 1 := by rw [Real.sin_sq_add_cos_sq]
          _ = 2 := by ring
      have h_sqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      have h_sq_sqrt : (Real.sqrt 2)^2 = 2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
      rw [← h_sq_sqrt] at h_sq
      exact abs_le_of_sq_le_sq h_sq h_sqrt_nonneg

    
    have h3_std : 2 * (x * x) + 4 * x + (-3) = 0 := by
      rw [← h3]; ring

    
    
    have disc_eq : discrim 2 4 (-3) = (2 * Real.sqrt 10) * (2 * Real.sqrt 10) := by
      simp [discrim]
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

    
    have quad_formula := quadratic_eq_zero_iff (by norm_num : (2 : ℝ) ≠ 0) disc_eq x
    rw [quad_formula] at h3_std

    
    have x_bound : abs x ≤ Real.sqrt 2 := by
      unfold x; exact sin_cos_bound

    
    
    

    
    
    
    

    
    
    have root1_satisfies : 2 * ((-2 + Real.sqrt 10) / 2)^2 + 4 * ((-2 + Real.sqrt 10) / 2) - 3 = 0 := by
      ring_nf
      simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
      norm_num

    
    
    

    
    cases' h3_std with h_root1 h_root2
    · 
      
      have h_simp : (-4 + 2 * Real.sqrt 10) / (2 * 2) = (-2 + Real.sqrt 10) / 2 := by
        ring
      rw [h_simp] at h_root1
      exact h_root1
    · 
      
      have h_simp : (-4 - 2 * Real.sqrt 10) / (2 * 2) = (-2 - Real.sqrt 10) / 2 := by
        ring
      rw [h_simp] at h_root2
      
      
      
      exfalso
      rw [h_root2] at x_bound
      
      have h_large : 2.5 < abs ((-2 - Real.sqrt 10) / 2) := by
        
        have h_neg : (-2 - Real.sqrt 10) / 2 < 0 := by
          have : 0 < Real.sqrt 10 := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 10)
          linarith
        rw [abs_of_neg h_neg]
        
        have h_sqrt_large : 3 < Real.sqrt 10 := by
          
          have : (3 : ℝ)^2 < 10 := by norm_num
          rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
          exact Real.sqrt_lt_sqrt (by norm_num) this
        linarith
      have h_small : Real.sqrt 2 < 2.5 := by
        
        
        have h_sq : 2 < (2.5 : ℝ)^2 := by norm_num
        
        rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 2.5)]
        exact h_sq
      
      have : Real.sqrt 2 < abs ((-2 - Real.sqrt 10) / 2) := by
        linarith [h_small, h_large]
      linarith [x_bound, this]

  have h5 : s * c = (5 - 2 * Real.sqrt 10) / 4 := by
    rw [h2, h4]
    ring_nf
    simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 10)]
    ring

  
  have h6 : (1 - s) * (1 - c) = 13/4 - Real.sqrt 10 := by
    
    have expand : (1 - s) * (1 - c) = 1 - (s + c) + s * c := by ring
    rw [expand]
    
    have subst_x : s + c = (-2 + Real.sqrt 10) / 2 := h4
    have subst_sc : s * c = (5 - 2 * Real.sqrt 10) / 4 := h5
    rw [subst_x, subst_sc]
    
    ring

  
  use 13, 4, 10
  constructor
  · 
    
    have : 13 = 3 * 4 + 1 := by norm_num
    rw [Nat.gcd_rec, this]
    simp [Nat.gcd_one_left]
  · 
    constructor
    · exact h6
    · norm_num
