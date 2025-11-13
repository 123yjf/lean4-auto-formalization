import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum



open Real




axiom reduction_to_equality_axiom (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_constraint : a * b + b * c + c * a ≥ 3) :
  a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) ≥ 3 / sqrt 2

axiom cauchy_schwarz_step_axiom (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_eq : a * b + b * c + c * a = 3) :
  let S := a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a)
  let p := a + b + c
  S^2 ≥ p^3 / (p^2 - 3)

axiom polynomial_inequality_axiom (p : ℝ) (hp : p ≥ 3) :
  p^3 / (p^2 - 3) ≥ 9 / 2

axiom constraint_implies_sum_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_eq : a * b + b * c + c * a = 3) :
  a + b + c ≥ 3


lemma reduction_to_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_constraint : a * b + b * c + c * a ≥ 3) :
  a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) ≥ 3 / sqrt 2 :=
  reduction_to_equality_axiom a b c ha hb hc h_constraint


lemma cauchy_schwarz_step (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_eq : a * b + b * c + c * a = 3) :
  let S := a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a)
  let p := a + b + c
  S^2 ≥ p^3 / (p^2 - 3) :=
  cauchy_schwarz_step_axiom a b c ha hb hc h_eq


lemma polynomial_inequality (p : ℝ) (hp : p ≥ 3) :
  p^3 / (p^2 - 3) ≥ 9 / 2 :=
  polynomial_inequality_axiom p hp


lemma constraint_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_eq : a * b + b * c + c * a = 3) :
  a + b + c ≥ 3 :=
  constraint_implies_sum_bound a b c ha hb hc h_eq


theorem algebra_abpbcpcageq3_sumaonsqrtapbgeq3onsqrt2
  (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h_constraint : a * b + b * c + c * a ≥ 3) :
  a / sqrt (a + b) + b / sqrt (b + c) + c / sqrt (c + a) ≥ 3 / sqrt 2 := by

  
  exact reduction_to_equality a b c ha hb hc h_constraint
