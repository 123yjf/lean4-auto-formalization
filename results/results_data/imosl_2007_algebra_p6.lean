import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

noncomputable section

namespace IMOSL


abbrev I := ZMod 100


@[simp] def succ (i : I) : I := i + 1


def S (a : I → ℝ) : ℝ := ∑ i, (a i)^2 * a (succ i)


def T (x : I → ℝ) : ℝ := ∑ i, x i * x (succ i)


 theorem imosl_2007_algebra_p6
    (a : I → ℝ)
    (hsum : ∑ i, (a i)^2 = (1 : ℝ)) :
    S a < (1 : ℝ) / 2 := by
  
  admit

end IMOSL
