import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic


def Good (k : Nat) : Prop :=
  ∀ n : Nat,
    Nat.Coprime (6*n + k) (6*n + 3) ∧
    Nat.Coprime (6*n + k) (6*n + 2) ∧
    Nat.Coprime (6*n + k) (6*n + 1)

lemma coprime_6n5_6n3 (n : Nat) :
    Nat.Coprime (6*n + 5) (6*n + 3) := by
  
  have h₂ : Nat.Coprime 2 (6*n + 3) := by
    
    have hE : Nat.Even (6*n) := by
      exact (Nat.even_mul.mpr (Or.inl (by decide)))
    have hO : Nat.Odd (6*n + 3) := (Nat.Even.add_odd hE (by decide))
    simpa [Nat.coprime_two_left] using hO
  
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    ((Nat.coprime_self_add_left (m := 6*n + 3) (n := 2))).mpr h₂


lemma coprime_6n5_6n2 (n : Nat) :
    Nat.Coprime (6*n + 5) (6*n + 2) := by
  
  have h3 : Nat.Coprime 3 (6*n + 2) := by
    
    
    have base : Nat.Coprime 3 2 := by decide
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
           Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      using (Nat.coprime_add_mul_right_right (m := 3) (n := 2) (k := 2*n)).mpr base
  
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using ((Nat.coprime_self_add_left (m := 6*n + 2) (n := 3))).mpr h3

lemma coprime_6n5_6n1 (n : Nat) :
    Nat.Coprime (6*n + 5) (6*n + 1) := by
  
  have h₁ : (6*n + 1) ≤ (6*n + 5) := by
    exact Nat.add_le_add_left (by decide : 1 ≤ 5) (6*n)
  have : Nat.Coprime (6*n + 5) 4 := by
    
    have hE : Nat.Even (6*n) := (Nat.even_mul.mpr (Or.inl (by decide)))
    have hO : Nat.Odd (6*n + 1) := (Nat.Even.add_odd hE (by decide))
    have h2 : Nat.Coprime 2 (6*n + 1) := by simpa [Nat.coprime_two_left] using hO
    
    have := (Nat.coprime_pow_left_iff (by decide : 0 < 2) 2 (6*n + 1)).2 h2
    simpa using this
  
  have := (Nat.coprime_self_sub_right (m := 6*n + 1) (n := 6*n + 5) h₁).mpr this
  
  simpa [Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this


lemma good_5 : Good 5 := by
  intro n; refine ⟨coprime_6n5_6n3 n, coprime_6n5_6n2 n, coprime_6n5_6n1 n⟩


lemma not_good_1 : ¬ Good 1 := by
  intro h
  have H := (h 1).2.2 
  have hc : ¬ Nat.Coprime (6*1 + 1) (6*1 + 1) := by decide
  exact hc H

lemma not_good_2 : ¬ Good 2 := by
  intro h
  have H := (h 0).2.1 
  have hc : ¬ Nat.Coprime (6*0 + 2) (6*0 + 2) := by decide
  exact hc H

lemma not_good_3 : ¬ Good 3 := by
  intro h
  have H := (h 0).1 
  have hc : ¬ Nat.Coprime (6*0 + 3) (6*0 + 3) := by decide
  exact hc H

lemma not_good_4 : ¬ Good 4 := by
  intro h
  have H := (h 0).2.1 
  have hc : ¬ Nat.Coprime (6*0 + 4) (6*0 + 2) := by decide
  exact hc H


theorem mathd_numbertheory_435_result :
    Good 5 ∧ ¬ Good 1 ∧ ¬ Good 2 ∧ ¬ Good 3 ∧ ¬ Good 4 := by
  exact ⟨good_5, not_good_1, not_good_2, not_good_3, not_good_4⟩
