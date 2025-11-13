import Mathlib.Data.Real.Basic
import Mathlib.Tactic




theorem aime_1983_p2 (p : ℝ) (hp_pos : 0 < p) (hp_lt : p < 15) :
  ∃ x₀ ∈ Set.Icc p 15, ∀ x ∈ Set.Icc p 15,
    |x₀ - p| + |x₀ - 15| + |x₀ - (p + 15)| ≤ |x - p| + |x - 15| + |x - (p + 15)| ∧
    |x₀ - p| + |x₀ - 15| + |x₀ - (p + 15)| = 15 := by
  let f := fun x : ℝ => |x - p| + |x - 15| + |x - (p + 15)|
  
  have fx_eq (x : ℝ) (hx : x ∈ Set.Icc p 15) : f x = 30 - x := by
    have hx_ge_p  : 0 ≤ x - p := sub_nonneg.mpr hx.1
    have hx_le_15 : x - 15 ≤ 0 := sub_nonpos.mpr hx.2
    have hx_le_p15 : x - (p + 15) ≤ 0 := by
      
      have h15_lt_p15 : (15 : ℝ) < p + 15 := by linarith [hp_pos]
      exact sub_nonpos.mpr (le_trans hx.2 (le_of_lt h15_lt_p15))
    have h : f x = (x - p) + (15 - x) + ((p + 15) - x) := by
      unfold f
      rw [abs_of_nonneg hx_ge_p, abs_of_nonpos hx_le_15, abs_of_nonpos hx_le_p15]
      ring
    calc
      f x = (x - p) + (15 - x) + ((p + 15) - x) := h
      _   = 30 - x := by ring
  use 15
  constructor
  · rw [Set.mem_Icc]
    exact ⟨le_of_lt hp_lt, le_rfl⟩
  · intro x hx
    constructor
    · 
      have hx' := fx_eq x hx
      have h15 := fx_eq 15 ⟨le_of_lt hp_lt, le_rfl⟩
      change f 15 ≤ f x
      rw [h15, hx']
      norm_num
      linarith [hx.2]
    · 
      have h15 := fx_eq 15 ⟨le_of_lt hp_lt, le_rfl⟩
      change f 15 = 15
      rw [h15]
      norm_num
