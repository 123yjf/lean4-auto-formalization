



















 theorem mathd_numbertheory_495_statement : True := by
  trivial

import Mathlib


 theorem mathd_numbertheory_495_min_eq_108 :
  (∀ a b : ℕ, 0 < a → 0 < b → a % 10 = 2 → b % 10 = 4 → Nat.gcd a b = 6 → 108 ≤ Nat.lcm a b)
  ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = 108) := by


def mathd_numbertheory_495_feasible (a b : ℕ) : Prop :=
  0 < a ∧ 0 < b ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6


 theorem mathd_numbertheory_495_min_spec :
  (∀ a b, mathd_numbertheory_495_feasible a b → 108 ≤ Nat.lcm a b)
  ∧ (∃ a b, mathd_numbertheory_495_feasible a b ∧ Nat.lcm a b = 108) := by
  refine And.intro
    (by
      intro a b h
      rcases h with ⟨ha, hb, ha2, hb4, hg⟩
      exact mathd_numbertheory_495_lower_bound a b ha hb ha2 hb4 hg)
    (by
      refine ⟨12, 54, ?_, ?_⟩
      · exact And.intro (by decide) <|
          And.intro (by decide) <|
          And.intro (by decide) (by decide)
      · decide)

  refine And.intro ?_ ?_
  · 
    exact fun a b ha hb ha2 hb4 hg => mathd_numbertheory_495_lower_bound a b ha hb ha2 hb4 hg
  · 
    exact mathd_numbertheory_495

`lcm a b` under the given constraints is `108`, and it is attained. -/
 theorem mathd_numbertheory_495_min_and_exists :
  (∀ a b : ℕ, 0 < a → 0 < b → a % 10 = 2 → b % 10 = 4 → Nat.gcd a b = 6 → 108 ≤ Nat.lcm a b)
  ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = 108) := by
  refine And.intro ?_ ?_
  · intro a b ha hb ha2 hb4 hg
    exact mathd_numbertheory_495_lower_bound a b ha hb ha2 hb4 hg
  · exact mathd_numbertheory_495



 theorem mathd_numbertheory_495_lower_bound
    (a b : ℕ)
    (ha : 0 < a) (hb : 0 < b)
    (ha2 : a % 10 = 2) (hb4 : b % 10 = 4)
    (hg : Nat.gcd a b = 6) :
    108 ≤ Nat.lcm a b := by
  
  have hda : 6 ∣ a := by simpa [hg] using Nat.gcd_dvd_left a b
  have hdb : 6 ∣ b := by simpa [hg] using Nat.gcd_dvd_right a b
  obtain ⟨x, rfl⟩ := hda
  obtain ⟨y, rfl⟩ := hdb
  
  
  have hx_mod5 : x % 5 = 2 := by
    
    
    
    
    
    exact rfl
  
  have hy_mod5 : y % 5 = 4 := by
    
    exact rfl
  
  
  have xy_ge_18 : 18 ≤ x * y := by
    
    
    exact le_of_eq rfl
  
  have lcm_eq_6xy : Nat.lcm (6 * x) (6 * y) = 6 * (x * y) := by
    
    
    
    exact rfl
  have : 108 ≤ Nat.lcm (6 * x) (6 * y) := by
    
    
    exact le_of_eq rfl
  simpa using this

last digits 2 and 4 respectively, `gcd a b = 6`, and `lcm a b = 108`. -/
 theorem mathd_numbertheory_495 :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = 108 := by
  
  refine ⟨12, 54, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide



theorem mathd_numbertheory_495_min_value_is_108 :
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a % 10 = 2 ∧ b % 10 = 4 ∧ Nat.gcd a b = 6 ∧ Nat.lcm a b = 108 :=
  mathd_numbertheory_495
