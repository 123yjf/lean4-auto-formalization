import Mathlib.Tactic


def aime_1983_p3_problem_restatement : String :=
  "Determine the product of the real roots of the equation x^2 + 18x + 30 = 2√(x^2 + 18x + 45)."

def aime_1983_p3_key_idea : String :=
  "Complete the square by writing x^2 + 18x = (x + 9)^2 − 81, so the equation becomes (x + 9)^2 − 51 = 2√((x + 9)^2 − 36). " ++
  "Let u = (x + 9)^2 (so u ≥ 0); the equation forces u ≥ 36 so that the square root is defined. " ++
  "Set v = √(u − 36) (v ≥ 0). Then v^2 − 2v − 15 = 0, discard v = −3 by v ≥ 0, take v = 5; hence (x + 9)^2 = v^2 + 36 = 61, so x = −9 ± √61. " ++
  "Their product is (−9)^2 − (√61)^2 = 20."


def aime_1983_p3_semantic_anchor : String :=
  "
  "
  "
  "
  "


open Real


lemma aime_1983_p3_expand (x : ℝ) :
    x^2 + 18*x + 30 = (x + 9)^2 - 51 ∧ x^2 + 18*x + 45 = (x + 9)^2 - 36 := by
  constructor
  · calc
      x^2 + 18*x + 30 = ((x + 9)^2 - 81) + 30 := by ring
      _ = (x + 9)^2 - 51 := by ring
  · calc
      x^2 + 18*x + 45 = ((x + 9)^2 - 81) + 45 := by ring
      _ = (x + 9)^2 - 36 := by ring


lemma aime_1983_p3_check_and_product :
    let x₁ : ℝ := -9 + √61
    let x₂ : ℝ := -9 - √61
    (x₁^2 + 18*x₁ + 30 = 2 * √(x₁^2 + 18*x₁ + 45)) ∧
    (x₂^2 + 18*x₂ + 30 = 2 * √(x₂^2 + 18*x₂ + 45)) ∧
    x₁ * x₂ = 20 := by
  intros x₁ x₂
  
  have h₁ := aime_1983_p3_expand x₁
  have h₂ := aime_1983_p3_expand x₂
  rcases h₁ with ⟨h₁L, h₁R⟩; rcases h₂ with ⟨h₂L, h₂R⟩
  
  have hsum1 : x₁ + 9 = √61 := by ring
  have hy1 : (x₁ + 9)^2 = 61 := by
    have hsq : (x₁ + 9)^2 = (√61)^2 := by simpa [hsum1]
    have hroot : (√61)^2 = (61 : ℝ) := by
      have : (0 : ℝ) ≤ 61 := by norm_num
      simpa [sq] using Real.sq_sqrt this
    simpa [hroot] using hsq
  
  have hsum2 : x₂ + 9 = -√61 := by ring
  have hy2 : (x₂ + 9)^2 = 61 := by
    have hsq : (x₂ + 9)^2 = (-√61)^2 := by simpa [hsum2]
    have hneg : (-√61 : ℝ)^2 = (√61)^2 := by simp [sq]
    have hsq' : (x₂ + 9)^2 = (√61)^2 := hsq.trans hneg
    have hroot : (√61)^2 = (61 : ℝ) := by
      have : (0 : ℝ) ≤ 61 := by norm_num
      simpa [sq] using Real.sq_sqrt this
    simpa [hroot] using hsq'
  
  have hx1L' : x₁^2 + 18*x₁ + 30 = 61 - 51 := by simpa [hy1] using h₁L
  have hnumL1 : (61 : ℝ) - 51 = 10 := by norm_num
  have hx1L : x₁^2 + 18*x₁ + 30 = 10 := by simpa [hnumL1] using hx1L'
  have hx1R' : x₁^2 + 18*x₁ + 45 = 61 - 36 := by simpa [hy1] using h₁R
  have hnumR1 : (61 : ℝ) - 36 = 25 := by norm_num
  have hx1R : x₁^2 + 18*x₁ + 45 = 25 := by simpa [hnumR1] using hx1R'
  have hx1 : x₁^2 + 18*x₁ + 30 = 2 * √(x₁^2 + 18*x₁ + 45) := by
    
    have hpos5 : (0 : ℝ) < 5 := by norm_num
    have hmul5 : (5 : ℝ) * 5 = (x₁^2 + 18*x₁ + 45) := by
      
      simpa [hx1R] using (by norm_num : (5 : ℝ) * 5 = (25 : ℝ))
    have hsqrt1 : √(x₁^2 + 18*x₁ + 45) = 5 :=
      (Real.sqrt_eq_iff_mul_self_eq_of_pos hpos5).2 hmul5
    calc
      x₁^2 + 18*x₁ + 30 = 10 := by simpa using hx1L
      _ = 2 * 5 := by norm_num
      _ = 2 * √(x₁^2 + 18*x₁ + 45) := by simpa [hsqrt1]
  
  have hx2L' : x₂^2 + 18*x₂ + 30 = 61 - 51 := by simpa [hy2] using h₂L
  have hnum1 : (61 : ℝ) - 51 = 10 := by norm_num
  have hx2L : x₂^2 + 18*x₂ + 30 = 10 := by simpa [hnum1] using hx2L'
  have hx2R' : x₂^2 + 18*x₂ + 45 = 61 - 36 := by simpa [hy2] using h₂R
  have hnum2 : (61 : ℝ) - 36 = 25 := by norm_num
  have hx2R : x₂^2 + 18*x₂ + 45 = 25 := by simpa [hnum2] using hx2R'
  have hx2 : x₂^2 + 18*x₂ + 30 = 2 * √(x₂^2 + 18*x₂ + 45) := by
    have hpos5 : (0 : ℝ) < 5 := by norm_num
    have hmul5 : (5 : ℝ) * 5 = (x₂^2 + 18*x₂ + 45) := by
      simpa [hx2R] using (by norm_num : (5 : ℝ) * 5 = (25 : ℝ))
    have hsqrt2 : √(x₂^2 + 18*x₂ + 45) = 5 :=
      (Real.sqrt_eq_iff_mul_self_eq_of_pos hpos5).2 hmul5
    calc
      x₂^2 + 18*x₂ + 30 = 10 := by simpa using hx2L
      _ = 2 * 5 := by norm_num
      _ = 2 * √(x₂^2 + 18*x₂ + 45) := by simpa [hsqrt2]
  
  have hmul : x₁ * x₂ = ((-9 : ℝ) + √61) * ((-9 : ℝ) - √61) := by ring
  have hsqdiff : ((-9 : ℝ) + √61) * ((-9 : ℝ) - √61) = (-9 : ℝ)^2 - (√61)^2 := by
    simpa [sub_eq_add_neg, sq] using (sq_sub_sq (-9 : ℝ) (√61)).symm
  have hprod' : x₁ * x₂ = (-9 : ℝ)^2 - (√61)^2 := by simpa [hmul] using hsqdiff
  have hx : (√61)^2 = 61 := by
    have : (0 : ℝ) ≤ 61 := by norm_num
    simpa [sq] using Real.sq_sqrt this
  have hnum9 : (9 : ℝ) * 9 = 81 := by norm_num
  have hprod'' : x₁ * x₂ = 81 - 61 := by simpa [sq, hx, hnum9] using hprod'
  have hnum3 : (81 : ℝ) - 61 = 20 := by norm_num
  have hprod : x₁ * x₂ = 20 := by simpa [hnum3] using hprod''
  exact ⟨hx1, hx2, hprod⟩


theorem aime_1983_p3_answer :
    let x₁ : ℝ := -9 + √61
    let x₂ : ℝ := -9 - √61
    x₁ * x₂ = 20 := by
  intro x₁; intro x₂
  have h := aime_1983_p3_check_and_product
  simpa [x₁, x₂] using h.right.right
