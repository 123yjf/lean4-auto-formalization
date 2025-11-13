import Mathlib.Data.Complex.Basic
import Mathlib.Tactic


theorem mathd_algebra_313 :
    ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I)
      = (1 : ℂ) / 5 + (3 : ℂ) / 5 * Complex.I := by
  
  have hstep :
      ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I)
        = (((1 : ℂ) + Complex.I) * (Complex.conj ((2 : ℂ) - Complex.I))) /
            (Complex.normSq ((2 : ℂ) - Complex.I)) := by
    
    have := by
      calc
        ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I)
            = ((1 : ℂ) + Complex.I) * ((2 : ℂ) - Complex.I)⁻¹ := by
                simpa [div_eq_mul_inv]
        _ = ((1 : ℂ) + Complex.I) *
              ((Complex.conj ((2 : ℂ) - Complex.I)) /
                (Complex.normSq ((2 : ℂ) - Complex.I))) := by
                simpa [Complex.inv_def]
    
    simpa using
      (mul_div_assoc ((1 : ℂ) + Complex.I)
        (Complex.conj ((2 : ℂ) - Complex.I))
        (Complex.normSq ((2 : ℂ) - Complex.I)))
  
  have hconj : Complex.conj ((2 : ℂ) - Complex.I) = (2 : ℂ) + Complex.I := by simp
  have hnorm : Complex.normSq ((2 : ℂ) - Complex.I) = (5 : ℝ) := by
    
    simp [Complex.normSq, pow_two]
  
  have hmain : ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I)
      = (((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I)) / (5 : ℂ) := by
    
    simpa [hconj, hnorm] using hstep
  
  have hnum : ((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I)
      = (1 : ℂ) + (3 : ℂ) * Complex.I := by
    
    have hIi : Complex.I * Complex.I = (-1 : ℂ) := by simpa using Complex.I_mul_I
    calc
      ((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I)
          = (1 : ℂ) * (2 : ℂ) + (1 : ℂ) * Complex.I + Complex.I * (2 : ℂ) + Complex.I * Complex.I := by
            ring
      _ = (2 : ℂ) + Complex.I + (2 : ℂ) * Complex.I + (-1 : ℂ) := by
            simp [hIi]
      _ = (1 : ℂ) + (3 : ℂ) * Complex.I := by ring
  
  calc
    ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I)
        = (((1 : ℂ) + Complex.I) * ((2 : ℂ) + Complex.I)) / (5 : ℂ) := hmain
    _ = ((1 : ℂ) + (3 : ℂ) * Complex.I) / (5 : ℂ) := by simpa [hnum]
    _ = (1 : ℂ) / (5 : ℂ) + ((3 : ℂ) * Complex.I) / (5 : ℂ) := by
          simpa using (add_div (1 : ℂ) ((3 : ℂ) * Complex.I) (5 : ℂ))
    _ = (1 : ℂ) / 5 + (3 : ℂ) / 5 * Complex.I := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (congrArg (fun z => (1 : ℂ) / (5 : ℂ) + z)
              (mul_div_assoc (3 : ℂ) Complex.I (5 : ℂ)))


 theorem mathd_algebra_313_VZ :
     let V := (1 : ℂ) + Complex.I
     let Z := (2 : ℂ) - Complex.I
     let I := V / Z
     I = (1 : ℂ) / 5 + (3 : ℂ) / 5 * Complex.I := by
   intro V Z I
   dsimp [V, Z, I]
   simpa using mathd_algebra_313


 theorem mathd_algebra_313_from_VIZ :
     let V := (1 : ℂ) + Complex.I
     let Z := (2 : ℂ) - Complex.I
     ∀ I : ℂ, V = I * Z → I = (1 : ℂ) / 5 + (3 : ℂ) / 5 * Complex.I := by
   intro V Z I h
   dsimp [V, Z] at h
   
   have hz : ((2 : ℂ) - Complex.I) ≠ 0 := by
     intro hz0
     have : (-1 : ℝ) = 0 := by
       simpa [hz0] using (by
         have := (by simp : Complex.im ((2 : ℂ) - Complex.I) = (-1 : ℝ))
         exact this)
     exact (neg_ne_zero.mpr (one_ne_zero : (1 : ℝ) ≠ 0)) this
   
   have : I = ((1 : ℂ) + Complex.I) / ((2 : ℂ) - Complex.I) := by
     have := congrArg (fun z : ℂ => z * ((2 : ℂ) - Complex.I)⁻¹) h
     
     simpa [mul_left_comm, mul_assoc, div_eq_mul_inv, hz] using this
   
   exact this.trans mathd_algebra_313
