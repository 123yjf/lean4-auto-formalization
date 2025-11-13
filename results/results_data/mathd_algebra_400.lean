import Mathlib.Tactic

@[simp] def pct (p a : ℚ) : ℚ := (p / 100) * a



theorem mathd_algebra_400 {x : ℚ}
    (h : (5 : ℚ) + pct 500 10 = pct 110 x) :
    x = 50 := by
  
  have h' : (11 / 10 : ℚ) * x = 55 := by
    simpa [pct,
           show (500 / 100 : ℚ) = 5 by norm_num,
           show (110 / 100 : ℚ) = (11 / 10 : ℚ) by norm_num,
           show (5 : ℚ) + 5 * 10 = 55 by norm_num] using h.symm
  
  have hx : x = (10 / 11 : ℚ) * 55 := by
    have := congrArg (fun t : ℚ => (10 / 11 : ℚ) * t) h'
    simpa [mul_assoc, mul_comm, mul_left_comm,
           show (10 / 11 : ℚ) * (11 / 10 : ℚ) = 1 by norm_num] using this
  
  simpa [show (10 / 11 : ℚ) * 55 = 50 by norm_num] using hx
