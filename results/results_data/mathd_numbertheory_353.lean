import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring





def S : ℕ := (Finset.range (4018 - 2010 + 1)).sum (fun i => 2010 + i)


lemma sum_formula : S = (4018 - 2010 + 1) * ((2010 + 4018) / 2) := by
  
  
  
  
  unfold S
  
  have h1 : (Finset.range (4018 - 2010 + 1)).sum (fun i => 2010 + i) =
            (Finset.range 2009).sum (fun i => 2010 + i) := by
    congr 2
  rw [h1]
  
  have h2 : (Finset.range 2009).sum (fun i => 2010 + i) =
            2009 * 2010 + (Finset.range 2009).sum (fun i => i) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range]
    ring
  rw [h2, Finset.sum_range_id]
  
  
  


lemma arithmetic_progression_method : S = 2009 * 3014 := by
  
  
  rw [sum_formula]
  


theorem mathd_numbertheory_353 : 2009 ∣ S := by
  
  rw [arithmetic_progression_method]
  
  exact dvd_mul_right 2009 3014




lemma modular_congruences :
  ∀ k : ℕ, k ≤ 2008 → (2010 + k) ≡ (k + 1) [MOD 2009] := by
  intro k _
  
  
  rw [Nat.ModEq]
  have h : 2010 + k = 2009 + (k + 1) := by ring
  rw [h, Nat.add_mod_left]




lemma last_term_congruence : 4018 ≡ 0 [MOD 2009] := by
  
  rw [Nat.modEq_zero_iff_dvd]
  
  exact ⟨2, by norm_num⟩


lemma verify_arithmetic : 4018 - 2010 + 1 = 2009 ∧ (2010 + 4018) / 2 = 3014 := by
  constructor <;> norm_num

lemma verify_modular : 2010 = 2009 + 1 ∧ 4018 = 2 * 2009 := by
  constructor <;> norm_num
