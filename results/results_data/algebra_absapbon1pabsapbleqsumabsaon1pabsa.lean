import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

theorem abs_div_ineq (a b : ℝ) :
  |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by
  
  let x := |a|
  let y := |b|
  
  let g : ℝ → ℝ := fun t => t / (1 + t)

  
  have hx : 0 ≤ x := abs_nonneg a
  have hy : 0 ≤ y := abs_nonneg b

  
  
  
  have h1 : 0 < 1 + |a + b| := by linarith [abs_nonneg (a + b)]
  have h2 : 0 < 1 + x := by linarith [hx]
  have h3 : 0 < 1 + y := by linarith [hy]

  
  have triangle : |a + b| ≤ x + y := abs_add a b

  
  

  
  have triangle : |a + b| ≤ x + y := abs_add a b

  
  

  
  
  have subadditivity : (x + y) / (1 + (x + y)) ≤ x / (1 + x) + y / (1 + y) := by
    
    have h_pos1 : 0 < 1 + (x + y) := by linarith [hx, hy]
    have h_pos2 : 0 < (1 + x) * (1 + y) := by
      apply mul_pos
      · linarith [hx]
      · linarith [hy]

    
    rw [div_add_div x y (ne_of_gt h2) (ne_of_gt h3)]

    
    rw [div_le_div_iff₀ h_pos1 h_pos2]

    
    ring_nf
    
    
    
    
    linarith [mul_nonneg hx hy, mul_nonneg (mul_nonneg hx hy) (by linarith [hx, hy] : 0 ≤ 2 + x + y)]

  
  have mono : |a + b| / (1 + |a + b|) ≤ (x + y) / (1 + (x + y)) := by
    
    
    have mono_func : ∀ s t : ℝ, 0 ≤ s → s ≤ t → s / (1 + s) ≤ t / (1 + t) := by
      intros s t hs hst
      
      rw [div_le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one hs)
                          (add_pos_of_pos_of_nonneg zero_lt_one (le_trans hs hst))]
      ring_nf
      
      linarith
    apply mono_func
    · exact abs_nonneg (a + b)
    · exact triangle

  
  exact le_trans mono subadditivity
