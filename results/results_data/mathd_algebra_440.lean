import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

noncomputable section


def jasminePintsPer3Miles : ℚ := (3 : ℚ) / 2


def jasmineWaterForMiles (miles : ℚ) : ℚ := jasminePintsPer3Miles * (miles / 3)


theorem mathd_algebra_440 : jasmineWaterForMiles 10 = 5 := by
  
  have : ((3 : ℚ) / 2) * (10 / 3) = (5 : ℚ) := by norm_num
  simpa [jasmineWaterForMiles, jasminePintsPer3Miles] using this

end
