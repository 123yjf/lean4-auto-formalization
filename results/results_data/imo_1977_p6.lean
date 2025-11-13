import Mathlib.Data.Nat.Basic












def Imo1977P6.Good (f : ℕ → ℕ) : Prop :=
  ∀ ⦃n : ℕ⦄, 1 ≤ n → f (n + 1) > f (f n)

namespace Imo1977P6



lemma id_isGood : Imo1977P6.Good (fun n => n) := by
  intro n hn
  
  exact Nat.lt_succ_self n

end Imo1977P6
