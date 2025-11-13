import Mathlib.Tactic





 theorem problem_mathd_algebra_296_area_change_eq :
     ((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2 = -3600 :=
   mathd_algebra_296

 theorem problem_mathd_algebra_296_area_decreases_by_3600 :
     Int.abs (((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2) = 3600 :=
   mathd_algebra_296_abs_change


 def oldArea : ℤ := (3491:ℤ) * 3491
 def newArea : ℤ := ((3491:ℤ) - 60) * ((3491:ℤ) + 60)

 theorem area_change_value : newArea - oldArea = -3600 := by
  simpa [oldArea, newArea, pow_two] using mathd_algebra_296

 theorem area_change_magnitude : Int.abs (newArea - oldArea) = 3600 := by
  simpa [oldArea, newArea] using mathd_algebra_296_abs_change


theorem mathd_algebra_296 :
    ((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2 = -3600 := by
  
  have h : ((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2 = - (60:ℤ)^2 := by
    ring
  have h60 : (60:ℤ)^2 = 3600 := by norm_num
  simpa [h60]



 theorem mathd_algebra_296_calc :
     ((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2 = -3600 := by
  have h : ((3491:ℤ) - 60) * ((3491:ℤ) + 60) = (3491:ℤ)^2 - (60:ℤ)^2 := by
    ring
  calc
    ((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2
        = ((3491:ℤ)^2 - (60:ℤ)^2) - (3491:ℤ)^2 := by simpa [h]
    _ = - (60:ℤ)^2 := by ring
    _ = -3600 := by norm_num


 theorem mathd_algebra_296_abs_change :
     |((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2| = 3600 := by
  have h := mathd_algebra_296
  have eq1 : |((3491:ℤ) - 60) * ((3491:ℤ) + 60) - (3491:ℤ)^2| = |-(3600:ℤ)| := by
    simpa [h]
  have eq2 : |-(3600:ℤ)| = (3600:ℤ) := by norm_num
  exact eq1.trans eq2



lemma diffSquares_sub_sq (x y : ℤ) : (x - y) * (x + y) - x^2 = - y^2 := by
  ring


 theorem areaChange_eq_3491_square_to_rect :
     ((3491 : ℤ) - 60) * (3491 + 60) - 3491^2 = -3600 := by
  have h : ((3491 : ℤ) - 60) * (3491 + 60) - 3491^2 = - (60^2 : ℤ) := by
    simpa using diffSquares_sub_sq (3491 : ℤ) 60
  have h60 : (60^2 : ℤ) = 3600 := by norm_num
  simpa [h60] using h

 theorem areaChange_abs_3491_square_to_rect :
     Int.abs (((3491 : ℤ) - 60) * (3491 + 60) - 3491^2) = 3600 := by
  have h := areaChange_eq_3491_square_to_rect
  simpa using congrArg Int.abs h
