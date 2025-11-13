import Mathlib.Data.Real.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic


theorem amgm_sum_to_product_bound (n : ℕ) (hn : 0 < n) (a : Fin n → ℝ)
  (h_nonneg : ∀ i, 0 ≤ a i) (h_sum : ∑ i, a i = n) :
  ∏ i, a i ≤ 1 := by
  
  
  by_cases h_zero : ∃ i, a i = 0
  · 
    obtain ⟨i, hi⟩ := h_zero
    rw [Finset.prod_eq_zero (Finset.mem_univ i)]
    · exact zero_le_one
    · exact hi
  · 
    
    push_neg at h_zero
    have h_pos : ∀ i, 0 < a i := by
      intro i
      exact lt_of_le_of_ne (h_nonneg i) (h_zero i).symm
    
    
    
    have n_cast_pos : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have prod_pos : 0 < ∏ i, a i := Finset.prod_pos (fun i _ => h_pos i)
    
    have h_weights : ∀ i ∈ (@Finset.univ (Fin n) _), 0 ≤ (1 : ℝ) / n := by
      intro i _
      exact div_nonneg zero_le_one (le_of_lt n_cast_pos)
    have h_weight_sum : ∑ i ∈ (@Finset.univ (Fin n) _), (1 : ℝ) / n = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul]
      rw [mul_div_cancel₀]
      exact ne_of_gt n_cast_pos
    have h_nonneg_mem : ∀ i ∈ (@Finset.univ (Fin n) _), 0 ≤ a i := by
      intro i _
      exact h_nonneg i
    have h_amgm := Real.geom_mean_le_arith_mean_weighted (@Finset.univ (Fin n) _) (fun _ => (1 : ℝ) / n) a h_weights h_weight_sum h_nonneg_mem
    
    have lhs_eq : ∏ i ∈ (@Finset.univ (Fin n) _), a i ^ ((1 : ℝ) / n) = (∏ i, a i) ^ (1 / n : ℝ) := by
      
      exact Real.finset_prod_rpow (@Finset.univ (Fin n) _) a h_nonneg_mem (1 / n)
    
    
    have h_sum_weights_times_a : ∑ i ∈ (@Finset.univ (Fin n) _), (1 : ℝ) / n * a i = 1 := by
      
      rw [← Finset.mul_sum]
      rw [h_sum]
      rw [div_mul_cancel₀]
      exact ne_of_gt n_cast_pos
    
    have h_prod_pow : ∏ i ∈ (@Finset.univ (Fin n) _), a i ^ ((1 : ℝ) / n) = (∏ i, a i) ^ (1 / n : ℝ) := by
      
      
      exact Real.finset_prod_rpow (@Finset.univ (Fin n) _) a h_nonneg_mem (1 / n)
    
    rw [h_prod_pow, h_sum_weights_times_a] at h_amgm
    
    have h_one_div_n_pos : (0 : ℝ) < 1 / n := div_pos zero_lt_one n_cast_pos
    have h_prod_nonneg : 0 ≤ ∏ i, a i := le_of_lt prod_pos
    
    
    have h_rpow_iff : (∏ i, a i) ^ (1 / n : ℝ) ≤ (1 : ℝ) ^ (1 / n : ℝ) ↔ ∏ i, a i ≤ 1 :=
      Real.rpow_le_rpow_iff h_prod_nonneg zero_le_one h_one_div_n_pos
    rw [Real.one_rpow] at h_rpow_iff
    exact h_rpow_iff.mp h_amgm
