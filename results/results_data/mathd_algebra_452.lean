






import Mathlib.Data.Rat.Basic
import Mathlib.Tactic







 theorem mathd_algebra_452 (a₁ a₅ a₉ d : ℚ)
    (h1 : a₁ = (2 : ℚ) / 3)
    (h9def : a₉ = a₁ + 8 * d)
    (h5def : a₅ = a₁ + 4 * d)
    (h9val : a₉ = 4 / 5) :
    a₅ = 11 / 15 := by
  
  have hcalc : (2 : ℚ) * a₅ = a₁ + a₉ := by
    have : (2 : ℚ) * (a₁ + 4 * d) = a₁ + (a₁ + 8 * d) := by ring
    simpa [h5def, h9def] using this
  
  have hhalf : a₅ = (1 / 2 : ℚ) * (a₁ + a₉) := by
    have := congrArg (fun x : ℚ => (1 / 2 : ℚ) * x) hcalc
    simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using this
  
  have : a₅ = (1 / 2 : ℚ) * ((2 : ℚ) / 3 + 4 / 5) := by simpa [h1, h9val] using hhalf
  have : a₅ = 11 / 15 := by simpa using (this.trans (by norm_num))
  exact this
