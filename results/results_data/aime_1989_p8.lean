import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

open scoped BigOperators


theorem aime_1989_p8
    (x : ℕ → ℝ)
    (h0 : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 0)^2 = 1)
    (h1 : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12)
    (h2 : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123) :
    ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 3)^2 = 334 := by
  
  
  have base_id : ∀ t : ℝ, (t + 3)^2 = t^2 - 3 * (t + 1)^2 + 3 * (t + 2)^2 := by
    intro t; ring
  
  set s := (Finset.Icc 1 7) with hs
  
  let S : ℕ → ℝ := fun k => ∑ i ∈ s, x i * ((i : ℝ) + k)^2
  
  have hS0 : S 0 = 1 := by simpa [S, hs, add_zero]
    using (by simpa [add_zero] using h0)
  have hS1 : S 1 = 12 := by simpa [S, hs] using h1
  have hS2 : S 2 = 123 := by simpa [S, hs] using h2
  have H₁ :
      ∑ i ∈ s, x i * ((i : ℝ) + 3)^2
        = ∑ i ∈ s, x i * ((i : ℝ)^2 - 3 * ((i : ℝ) + 1)^2 + 3 * ((i : ℝ) + 2)^2) := by
    apply Finset.sum_congr rfl
    intro i hi
    
    simpa [mul_add, add_mul, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z => x i * z) (base_id (i : ℝ))
  have H₂ :
      ∑ i ∈ s, x i * ((i : ℝ) + 3)^2
        = (∑ i ∈ s, x i * (i : ℝ)^2)
          - 3 * (∑ i ∈ s, x i * ((i : ℝ) + 1)^2)
          + 3 * (∑ i ∈ s, x i * ((i : ℝ) + 2)^2) := by
    classical
    simpa [sub_eq_add_neg, Finset.sum_add_distrib, Finset.mul_sum, mul_add, add_mul,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using H₁
  
  have hS0 : ∑ i ∈ s, x i * (i : ℝ)^2 = 1 := by
    simpa [hs] using (by simpa using h0)
  have hS1 : ∑ i ∈ s, x i * ((i : ℝ) + 1)^2 = 12 := by simpa [hs] using h1
  have hS2 : ∑ i ∈ s, x i * ((i : ℝ) + 2)^2 = 123 := by simpa [hs] using h2
  have hlin : ∑ i ∈ s, x i * ((i : ℝ) + 3)^2
      = (1 : ℝ) - 3 * 12 + 3 * 123 := by
    have := H₂
    simpa [hS0, hS1, hS2] using this
  have hnum : (1 : ℝ) - 3 * 12 + 3 * 123 = 334 := by
    norm_num
  simpa [hs] using hlin.trans hnum



theorem aime_1989_p8_S (x : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 0)^2 = 1) →
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12) →
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123) →
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 3)^2 = 334) := by
  intro h0 h1 h2
  simpa using aime_1989_p8 x h0 h1 h2


namespace AIME1989P8


def S (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + k)^2


 theorem compute_S3 {x : ℕ → ℝ}
    (h0 : S x 0 = 1) (h1 : S x 1 = 12) (h2 : S x 2 = 123) :
    S x 3 = 334 := by
  
  have h0' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 0)^2 = 1 := by
    simpa [S, add_zero]
      using h0
  have h1' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12 := by
    simpa [S] using h1
  have h2' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123 := by
    simpa [S] using h2
  simpa [S] using aime_1989_p8 x h0' h1' h2'

end AIME1989P8



theorem aime_1989_p8_restate (x : ℕ → ℝ) :
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 0)^2 = 1) ∧
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12) ∧
    (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123)
    → (∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 3)^2 = 334) := by
  intro h
  rcases h with ⟨h0, h1, h2⟩
  exact aime_1989_p8 x h0 h1 h2



noncomputable def Sk (x : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 7, x i * (((i + k : ℕ) : ℝ) ^ 2)


 theorem aime_1989_p8_let_style (x : ℕ → ℝ) :
  (let S0 := Sk x 0; let S1 := Sk x 1; let S2 := Sk x 2 in
    S0 = 1 → S1 = 12 → S2 = 123 → Sk x 3 = 334) := by
  intro h0 h1 h2
  
  have h0' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 0)^2 = 1 := by
    simpa [Sk, add_zero, Nat.cast_add, Nat.cast_ofNat]
      using h0
  have h1' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12 := by
    simpa [Sk, Nat.cast_add, Nat.cast_ofNat]
      using h1
  have h2' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123 := by
    simpa [Sk, Nat.cast_add, Nat.cast_ofNat]
      using h2
  simpa [Sk, Nat.cast_add, Nat.cast_ofNat]
    using aime_1989_p8 x h0' h1' h2'


namespace AIME1989P8


noncomputable def S0 (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 7, x i * (i : ℝ)^2
noncomputable def S1 (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2
noncomputable def S2 (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2
noncomputable def S3 (x : ℕ → ℝ) : ℝ := ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 3)^2


 theorem S012_to_S3 (x : ℕ → ℝ)
    (h0 : S0 x = 1) (h1 : S1 x = 12) (h2 : S2 x = 123) :
    S3 x = 334 := by
  have h0' : ∑ i ∈ Finset.Icc 1 7, x i * (i : ℝ)^2 = 1 := by simpa [S0]
  have h1' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 1)^2 = 12 := by simpa [S1]
  have h2' : ∑ i ∈ Finset.Icc 1 7, x i * ((i : ℝ) + 2)^2 = 123 := by simpa [S2]
  simpa [S3] using aime_1989_p8 x h0' h1' h2'


 theorem S012_and_to_S3 (x : ℕ → ℝ) :
    (S0 x = 1) ∧ (S1 x = 12) ∧ (S2 x = 123) → S3 x = 334 := by
  intro h; rcases h with ⟨h0, h1, h2⟩; exact S012_to_S3 x h0 h1 h2

end AIME1989P8
