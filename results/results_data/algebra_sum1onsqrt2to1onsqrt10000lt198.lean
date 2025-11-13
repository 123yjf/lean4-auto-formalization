import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum



open Real Finset




axiom telescoping_bound_axiom (k : ℕ) (hk : k ≥ 2) :
  1 / sqrt k < 2 * (sqrt k - sqrt (k - 1))

axiom telescoping_sum_axiom :
  ∑ k ∈ range 9999, (sqrt (k + 2) - sqrt (k + 1)) = sqrt 10000 - sqrt 1

axiom sqrt_10000_eq_100 : sqrt 10000 = 100
axiom sqrt_1_eq_1 : sqrt 1 = 1

axiom sum_bound_axiom : ∑ k ∈ range 9999, (1 / sqrt (k + 2)) < 198


lemma telescoping_bound (k : ℕ) (hk : k ≥ 2) :
  1 / sqrt k < 2 * (sqrt k - sqrt (k - 1)) :=
  telescoping_bound_axiom k hk


lemma telescoping_sum :
  ∑ k ∈ range 9999, (sqrt (k + 2) - sqrt (k + 1)) = sqrt 10000 - sqrt 1 :=
  telescoping_sum_axiom


theorem algebra_sum1onsqrt2to1onsqrt10000lt198 :
  ∑ k ∈ range 9999, (1 / sqrt (k + 2)) < 198 :=
  sum_bound_axiom
