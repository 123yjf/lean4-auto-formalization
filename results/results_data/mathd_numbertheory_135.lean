import Mathlib


def nineDigit (A B C : Nat) : Nat :=
  10^8 * A + 10^7 * B + 10^6 * C + 10^5 * A + 10^4 * C + 10^3 * C + 10^2 * B + 10 * A + B


lemma pow3_17_10_eval : 3^17 + 3^10 = 129199212 := by decide


theorem mathd_numbertheory_135 :
    ∃ A B C : Nat, nineDigit A B C = 3^17 + 3^10 ∧ 100*A + 10*B + C = 129 := by
  refine ⟨1, 2, 9, ?_, by decide⟩
  
  have h₁ : nineDigit 1 2 9 = 129199212 := by decide
  have h₂ : 3^17 + 3^10 = 129199212 := pow3_17_10_eval
  exact h₁.trans h₂.symm
