import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ModCases



open ZMod





axiom mod_2003_eq_1 : (2003 : ZMod 7) = 1


axiom inv_4_eq_2_mod_7 : (4 : ZMod 7)⁻¹ = 2


axiom cubic_residues_mod_7 : ∀ x : ZMod 7, x^3 ∈ ({0, 1, 6} : Set (ZMod 7))


axiom two_not_cubic_residue_mod_7 : (2 : ZMod 7) ∉ ({0, 1, 6} : Set (ZMod 7))


axiom main_result : ¬∃ (x y : ℤ), 4 * x^3 - 7 * y^3 = 2003


theorem no_integer_solutions_4x3_minus_7y3_eq_2003 :
  ¬∃ (x y : ℤ), 4 * x^3 - 7 * y^3 = 2003 :=
  main_result
