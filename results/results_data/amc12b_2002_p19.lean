import Mathlib.Data.Real.Basic
import Mathlib.Tactic


theorem amc12b_2002_p19
    {a b c : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a * (b + c) = 152)
    (h2 : b * (c + a) = 162)
    (h3 : c * (a + b) = 170) :
    a * b * c = 720 := by
  
  set x := a * b with hx
  set y := b * c with hy
  set z := c * a with hz
  
  have hxz : x + z = 152 := by
    simpa [hx, hz, mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h1
  have hxy : x + y = 162 := by
    simpa [hx, hy, mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h2
  have hyz : y + z = 170 := by
    simpa [hy, hz, mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc] using h3
  
  have hy_sub_z : y - z = 10 := by linarith [hxy, hxz]
  have hy_val : y = 90 := by linarith [hyz, hy_sub_z]
  have hz_val : z = 80 := by linarith [hyz, hy_val]
  have hx_val : x = 72 := by linarith [hxy, hy_val]
  
  have hxyz_sq : x * y * z = (a * b * c) ^ 2 := by
    simpa [hx, hy, hz] using (by
      have : (a * b) * (b * c) * (c * a) = (a * b * c) ^ 2 := by ring
      exact this)
  
  have hxyz_num : x * y * z = 518400 := by
    have hnum : x * y * z = (72 : ℝ) * 90 * 80 := by simpa [hx_val, hy_val, hz_val]
    have hnum' : (72 : ℝ) * 90 * 80 = 518400 := by norm_num
    simpa [hnum'] using hnum
  
  have hsq : (a * b * c) ^ 2 = 518400 := by
    simpa [hxyz_num] using hxyz_sq.symm
  
  have hpos : 0 < a * b * c := by
    have hbc : 0 < b * c := mul_pos hb hc
    have habc : 0 < a * (b * c) := mul_pos ha hbc
    simpa [mul_assoc] using habc
  
  have habs : |a * b * c| = a * b * c := abs_of_nonneg (le_of_lt hpos)
  have hsqrtEq : a * b * c = Real.sqrt 518400 := by
    have hleft : Real.sqrt ((a * b * c) ^ 2) = |a * b * c| := by
      simpa [pow_two] using Real.sqrt_sq_eq_abs (a * b * c)
    have : Real.sqrt ((a * b * c) ^ 2) = Real.sqrt 518400 := by simpa [hsq]
    simpa [hleft, habs] using this
  
  have hsqrtVal : Real.sqrt 518400 = (720 : ℝ) := by norm_num
  simpa [hsqrtVal] using hsqrtEq
