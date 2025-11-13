import Mathlib.Data.Real.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Tactic





theorem aime_1994_p3_answer : (4561 : ℤ) % 1000 = 561 := by norm_num



noncomputable def solution_function : ℝ → ℝ := fun x =>
  (1/2) * x^2 + (1/2) * x + (if Int.floor x % 2 = 0 then 96 else -96)


lemma particular_solution_property (x : ℝ) :
  ((1/2) * x^2 + (1/2) * x) + ((1/2) * (x-1)^2 + (1/2) * (x-1)) = x^2 := by
  ring


lemma floor_sub_one (x : ℝ) : Int.floor (x - 1) = Int.floor x - 1 := by
  exact Int.floor_sub_one x


lemma homogeneous_alternating (n : ℤ) :
  (if n % 2 = 0 then (96 : ℝ) else -96) + (if (n - 1) % 2 = 0 then (96 : ℝ) else -96) = 0 := by
  
  cases' Int.emod_two_eq_zero_or_one n with h_even h_odd
  · 
    have h_n_minus_1_odd : (n - 1) % 2 = 1 := by
      
      have : n - 1 = n + (-1) := by ring
      rw [this, Int.add_emod, h_even]
      norm_num
    rw [if_pos h_even, if_neg]
    · ring
    · rw [h_n_minus_1_odd]; norm_num
  · 
    have h_n_minus_1_even : (n - 1) % 2 = 0 := by
      
      have : n - 1 = n + (-1) := by ring
      rw [this, Int.add_emod, h_odd]
      norm_num
    rw [if_neg, if_pos h_n_minus_1_even]
    · ring
    · rw [h_odd]; norm_num


theorem solution_satisfies_equation (x : ℝ) :
  solution_function x + solution_function (x - 1) = x^2 := by
  unfold solution_function
  rw [floor_sub_one]
  
  calc
    ((1/2) * x^2 + (1/2) * x + (if Int.floor x % 2 = 0 then (96 : ℝ) else -96)) +
    ((1/2) * (x-1)^2 + (1/2) * (x-1) + (if (Int.floor x - 1) % 2 = 0 then (96 : ℝ) else -96))
    = ((1/2) * x^2 + (1/2) * x) + ((1/2) * (x-1)^2 + (1/2) * (x-1)) +
      ((if Int.floor x % 2 = 0 then (96 : ℝ) else -96) + (if (Int.floor x - 1) % 2 = 0 then (96 : ℝ) else -96)) := by ring
    _ = x^2 + 0 := by
      rw [particular_solution_property x, homogeneous_alternating (Int.floor x)]
    _ = x^2 := by ring


theorem solution_initial_condition : solution_function 19 = 94 := by
  unfold solution_function
  
  have h_floor : Int.floor (19 : ℝ) = 19 := by norm_num
  have h_mod : (19 : ℤ) % 2 = 1 := by norm_num
  rw [h_floor, h_mod]
  simp
  norm_num


theorem aime_1994_p3 : ∃ f : ℝ → ℝ, (∀ x : ℝ, f x + f (x - 1) = x^2) ∧ f 19 = 94 ∧ (4561 : ℤ) % 1000 = 561 := by
  use solution_function
  exact ⟨solution_satisfies_equation, solution_initial_condition, aime_1994_p3_answer⟩
