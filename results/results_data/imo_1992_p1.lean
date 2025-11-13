

























import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace IMO1992P1


@[simp] def GoodTriple (p q r : ℕ) : Prop :=
  1 < p ∧ p < q ∧ q < r ∧ ((p - 1) * (q - 1) * (r - 1)) ∣ (p * q * r - 1)


lemma good_248 : GoodTriple 2 4 8 := by
  refine And.intro ?hp (And.intro ?hpq (And.intro ?hqr ?hdiv))
  · decide
  · decide
  · decide
  · 
    
    simpa using (show 21 ∣ 63 from ⟨3, by decide⟩)


lemma good_3515 : GoodTriple 3 5 15 := by
  refine And.intro ?hp (And.intro ?hpq (And.intro ?hqr ?hdiv))
  · decide
  · decide
  · decide
  · 
    
    simpa using (show 112 ∣ 224 from ⟨2, by decide⟩)

end IMO1992P1
