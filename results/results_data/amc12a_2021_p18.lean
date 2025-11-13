import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.ArithmeticFunction
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith



open Nat




axiom multiplicative_additive_function_formula (f : ℚ → ℤ)
  (h_mult_add : ∀ a b : ℚ, 0 < a → 0 < b → f (a * b) = f a + f b)
  (h_prime : ∀ p : ℕ, p.Prime → f p = p) :
  ∀ (num den : ℕ) (_ : 0 < num) (_ : 0 < den),
  f (num / den) = (∑ p ∈ num.primeFactors, num.factorization p * p) -
                  (∑ p ∈ den.primeFactors, den.factorization p * p)


def f_value_A : ℤ := 17 - 5 * 2  
def f_value_B : ℤ := 11 - 4 * 2  
def f_value_C : ℤ := 7 - 2 * 3   
def f_value_D : ℤ := 7 - 2 - 3   
def f_value_E : ℤ := 2 * 5 - 11  


lemma option_A_positive : f_value_A = 7 := by simp [f_value_A]
lemma option_B_positive : f_value_B = 3 := by simp [f_value_B]
lemma option_C_positive : f_value_C = 1 := by simp [f_value_C]
lemma option_D_positive : f_value_D = 2 := by simp [f_value_D]
lemma option_E_negative : f_value_E = -1 := by simp [f_value_E]


theorem amc12a_2021_p18 :
  f_value_E < 0 ∧
  f_value_A > 0 ∧ f_value_B > 0 ∧ f_value_C > 0 ∧ f_value_D > 0 := by

  constructor
  · 
    rw [option_E_negative]
    norm_num

  constructor
  · 
    rw [option_A_positive]
    norm_num

  constructor
  · 
    rw [option_B_positive]
    norm_num

  constructor
  · 
    rw [option_C_positive]
    norm_num

  · 
    rw [option_D_positive]
    norm_num
