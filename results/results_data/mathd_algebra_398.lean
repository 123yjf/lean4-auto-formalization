import Mathlib.Data.Rat.Basic
import Mathlib.Tactic



theorem mathd_algebra_398
    {lig lag lug : ℚ}
    (h1 : 7*lig = 4*lag)
    (h2 : 9*lag = 20*lug) :
    80*lug = 63*lig := by
  
  have hA : 80 * lug = 36 * lag := by
    calc
      80 * lug = (4 * 20) * lug := by norm_num
      _ = 4 * (20 * lug) := by ring
      _ = 4 * (9 * lag) := by
        simpa using congrArg (fun x => (4:ℚ) * x) h2.symm
      _ = (4 * 9) * lag := by ring
      _ = 36 * lag := by norm_num
  have hB : 36 * lag = 63 * lig := by
    calc
      36 * lag = (9 * 4) * lag := by norm_num
      _ = 9 * (4 * lag) := by ring
      _ = 9 * (7 * lig) := by
        simpa using congrArg (fun x => (9:ℚ) * x) h1.symm
      _ = (9 * 7) * lig := by ring
      _ = 63 * lig := by norm_num
  exact hA.trans hB



example : (80:ℚ) * (9/20) * (7/4) = (63:ℚ) := by norm_num



theorem convert_80_lugs_to_ligs
    {lig lag lug : ℚ}
    (h1 : 7*lig = 4*lag)
    (h2 : 9*lag = 20*lug) :
    80*lug = 63*lig :=
  mathd_algebra_398 h1 h2
