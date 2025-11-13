import Mathlib

open scoped BigOperators


theorem algebra_9onxpypzleqsum2onxpy
    (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    9 / (x + y + z) ≤ 2 / (x + y) + 2 / (y + z) + 2 / (z + x) := by
  
  set a : ℝ := x + y
  set b : ℝ := y + z
  set c : ℝ := z + x
  have ha : 0 < a := add_pos hx hy
  have hb : 0 < b := add_pos hy hz
  have hc : 0 < c := add_pos hz hx
  
  have hsum : a + b + c = 2 * (x + y + z) := by
    calc
      a + b + c = (x + y) + (y + z) + (z + x) := by simp [a, b, c]
      _ = 2 * x + 2 * y + 2 * z := by ring
      _ = 2 * (x + y + z) := by ring

  
  classical
  let w : Fin 3 → ℝ := fun i =>
    match i with
    | ⟨0, _⟩ => a
    | ⟨1, _⟩ => b
    | ⟨2, _⟩ => c
  have hw_pos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 < w i := by
    intro i _
    fin_cases i <;> simp [w, ha, hb, hc]
  have hTitu :=
    Finset.sq_sum_div_le_sum_sq_div (s := (Finset.univ : Finset (Fin 3)))
      (f := fun _ : Fin 3 => (1 : ℝ)) (g := w) hw_pos

  
  have h1 : (∑ i ∈ (Finset.univ : Finset (Fin 3)), (1 : ℝ)) = 3 := by simp
  have h2 : (∑ i ∈ (Finset.univ : Finset (Fin 3)), w i) = a + b + c := by
    simp [w, Fin.sum_univ_three]
  
  have hTitu' : (3 : ℝ) ^ 2 / (a + b + c) ≤ (∑ i : Fin 3, (w i)⁻¹) := by
    simpa [h1, h2] using hTitu
  have hsumInv : (∑ i : Fin 3, (w i)⁻¹) = 1 / a + 1 / b + 1 / c := by
    simp [w, Fin.sum_univ_three]
  have hcore : (3 : ℝ) ^ 2 / (a + b + c) ≤ 1 / a + 1 / b + 1 / c := by
    simpa [hsumInv] using hTitu'

  
  have hhalf : (3 : ℝ) ^ 2 / (2 * (x + y + z)) ≤ 1 / a + 1 / b + 1 / c := by
    simpa [hsum] using hcore
  have hmul : 2 * ((3 : ℝ) ^ 2 / (2 * (x + y + z))) ≤ 2 * (1 / a + 1 / b + 1 / c) :=
    mul_le_mul_of_nonneg_left hhalf (by norm_num : 0 ≤ (2 : ℝ))
  have hEq : 2 * ((3 : ℝ) ^ 2 / ((x + y + z) * 2)) = (3 : ℝ) ^ 2 / (x + y + z) := by
    have h2nz : (2 : ℝ) ≠ 0 := by norm_num
    simpa [mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using
      (mul_div_mul_left ((3 : ℝ) ^ 2) (x + y + z) h2nz)

  have hrewrite₁ : 2 * ((3 : ℝ) ^ 2 / (2 * (x + y + z))) = (3 : ℝ) ^ 2 / (x + y + z) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hEq
  have hfinal2 : (3 : ℝ) ^ 2 / (x + y + z) ≤ 2 * (1 / a + 1 / b + 1 / c) := by
    simpa [hrewrite₁] using hmul
  have hfinal : 9 / (x + y + z) ≤ 2 * (1 / a + 1 / b + 1 / c) := by
    have hstep : 3 * (3 / (x + y + z)) ≤ 2 * (1 / a + 1 / b + 1 / c) := by
      simpa [pow_two, mul_div_assoc] using hfinal2
    have h9 : (9 : ℝ) = 3 * 3 := by norm_num
    simpa [h9, mul_comm, mul_left_comm, mul_assoc, mul_div_assoc] using hstep
  have hfinalR : 9 / (x + y + z) ≤ (1 / a + 1 / b + 1 / c) * 2 := by
    simpa [mul_comm] using hfinal

  
  simpa [a, b, c, one_div, add_mul, add_comm, add_left_comm, add_assoc,
    mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hfinalR
