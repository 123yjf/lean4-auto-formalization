import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic


 theorem mathd_numbertheory_765 :
   IsGreatest {x : ℤ | ((24 : ZMod 1199) * (x : ZMod 1199) = (15 : ZMod 1199)) ∧ x < 0} (-449) := by
  
  refine ⟨?hmem, ?hmax⟩
  · constructor
    · 
      decide
    · decide
  
  intro y hy
  rcases hy with ⟨hy_congr, hy_neg⟩
  
  have hinv : (24 : ZMod 1199) * (50 : ZMod 1199) = 1 := by decide
  
  have hy_class : (y : ZMod 1199) = (750 : ZMod 1199) := by
    calc
      (y : ZMod 1199) = 1 * (y : ZMod 1199) := by simp
      _ = ((24 : ZMod 1199) * (50 : ZMod 1199)) * (y : ZMod 1199) := by simpa [hinv]
      _ = (24 : ZMod 1199) * ((50 : ZMod 1199) * (y : ZMod 1199)) := by ac_rfl
      _ = (50 : ZMod 1199) * ((24 : ZMod 1199) * (y : ZMod 1199)) := by ac_rfl
      _ = (50 : ZMod 1199) * (15 : ZMod 1199) := by simpa [hy_congr]
      _ = (750 : ZMod 1199) := by decide
  
  have hrep : ((-449 : ℤ) : ZMod 1199) = (750 : ZMod 1199) := by decide
  
  have hCong : ((y : ZMod 1199) = ((-449 : ℤ) : ZMod 1199)) := by
    simpa [hy_class] using hrep.symm
  
  
  have hDiv : (1199 : ℤ) ∣ (y - (-449)) := by
    
    
    
    
    
    
    simpa using (ZMod.intCast_zmod_eq_intCast_zmod_iff_dvd (n := 1199) (a := y) (b := -449)).1 hCong
  rcases hDiv with ⟨t, ht⟩
  
  have : y = -449 + 1199 * t := by
    have := congrArg (fun z => z + (-449)) ht
    
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using ht
  
  
  have : t ≤ 0 := by
    by_contra htpos
    have : 0 < t := lt_of_le_of_ne (le_of_not_gt htpos) (by decide)
    have : 0 ≤ 1199 * t := mul_nonneg (by decide : 0 ≤ (1199 : ℤ)) (le_of_lt this)
    have : y = -449 + 1199 * t := by simpa using this
    have : 0 < y := by
      have : 0 < 1199 * t := mul_pos (by decide : 0 < (1199 : ℤ)) (by exact this)
      have : -449 + 1199 * t > -449 + 0 := add_lt_add_left this _
      simpa using this
    exact lt_irrefl _ (lt_trans this hy_neg)
  
  have : y ≤ -449 := by
    
    rcases lt_or_eq_of_le this with htlt | hteq
    · have : 1199 * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by decide : 0 ≤ (1199 : ℤ)) (le_of_lt htlt)
      have := add_le_add_left this (-449)
      simpa [this] using this
    · simpa [hteq] using le_of_eq (by simpa [hteq] using this)
  exact this
