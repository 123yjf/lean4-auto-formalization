





import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Real


theorem mathd_algebra_320_eq :
    2 * (((2 : ℝ) + sqrt 22) / 2) ^ 2 = 4 * (((2 : ℝ) + sqrt 22) / 2) + 9 := by
  
  set s : ℝ := sqrt 22
  have hsq : s ^ 2 = 22 := by
    have h0 : (0 : ℝ) ≤ 22 := by norm_num
    simpa [s, pow_two] using Real.sqrt_mul_self h0
  have hpoly : (2 + s) ^ 2 = 4 * (2 + s) + 18 := by
    calc
      (2 + s) ^ 2 = 4 + 4 * s + s ^ 2 := by ring
      _ = 4 + 4 * s + 22 := by simpa [hsq]
      _ = 4 * (2 + s) + 18 := by ring
  calc
    2 * (((2 + s) / 2) ^ 2)
        = ((2 + s) ^ 2) / 2 := by field_simp [pow_two]
    _ = (4 * (2 + s) + 18) / 2 := by
          simpa using congrArg (fun t : ℝ => t / 2) hpoly
    _ = 2 * (2 + s) + 9 := by field_simp
    _ = 4 * (((2 + s) / 2)) + 9 := by field_simp


lemma mathd_algebra_320_pos : 0 < (((2 : ℝ) + sqrt 22) / 2) := by
  have : 0 < sqrt (22 : ℝ) := by
    have : 0 < (22 : ℝ) := by norm_num
    exact sqrt_pos.mpr this
  have : 0 < (2 : ℝ) + sqrt 22 := by linarith
  have h2pos : 0 < (2 : ℝ) := by norm_num
  exact (div_pos this h2pos)


private def α : ℝ := ((2 : ℝ) + sqrt 22) / 2
private def β : ℝ := ((2 : ℝ) - sqrt 22) / 2


lemma quad_factor (x : ℝ) : 2 * x^2 - 4 * x - 9 = 2 * (x - α) * (x - β) := by
  have hsq : (sqrt (22 : ℝ)) ^ 2 = 22 := by
    have h0 : (0 : ℝ) ≤ 22 := by norm_num
    simpa [pow_two] using Real.sqrt_mul_self h0
  
  ring_nf [α, β, pow_two, div_eq_mul_inv, hsq]


lemma quad_roots (x : ℝ) : 2 * x^2 - 4 * x - 9 = 0 ↔ x = α ∨ x = β := by
  have hf := quad_factor x
  constructor
  · intro hx
    have hprod : 2 * (x - α) * (x - β) = 0 := by simpa [hf]
    have h2ne : (2 : ℝ) ≠ 0 := by norm_num
    have : (x - α) * (x - β) = 0 := (mul_left_cancel₀ h2ne).1 (by simpa [mul_assoc] using hprod)
    exact (mul_eq_zero.mp this).imp (by simpa) (by simpa)
  · intro hx
    rcases hx with h | h
    · simpa [hf, h]
    · simpa [hf, h]


lemma beta_neg : β < 0 := by
  unfold β
  have hs : 0 < sqrt (22 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have : 2 - sqrt 22 < 0 := by linarith
  have h2 : 0 < (2 : ℝ) := by norm_num
  exact (div_neg_iff.2 ⟨this, h2.ne'⟩)


lemma pos_solution_eq_alpha {x : ℝ} (hxpos : 0 < x) (hxeq : 2 * x^2 = 4 * x + 9) : x = α := by
  
  have hx0' : 2 * x^2 - (4 * x + 9) = 0 := by
    simpa using congrArg (fun t : ℝ => t - (4 * x + 9)) hxeq
  have hx0 : 2 * x^2 - 4 * x - 9 = 0 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using hx0'
  have h := (quad_roots x).1 hx0
  rcases h with hα | hβ
  · exact hα
  · have hxpos' : 0 < β := by simpa [hβ] using hxpos
    have hβnotpos : ¬ 0 < β := not_lt.mpr (le_of_lt beta_neg)
    exact (hβnotpos hxpos').elim





theorem mathd_algebra_320_sum : (2 + 22 + 2 : ℕ) = 26 := by
  norm_num
