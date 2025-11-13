import Mathlib
open Finset


namespace AMC12A_2020_P7


@[simp] def separateArea : ℕ :=
  6 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2)

@[simp] def hiddenArea : ℕ :=
  2 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2)


lemma hiddenArea_interfaces : hiddenArea = 2 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2) := rfl
lemma separateArea_cubes : separateArea = 6 * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2) := rfl


 theorem amc12a_2020_p7 :
    separateArea - hiddenArea = 658 := by
  
  norm_num [separateArea, hiddenArea]

end AMC12A_2020_P7



namespace AMC12A_2020_P7

lemma separateArea_eval : separateArea = 840 := by
  simp [separateArea]

lemma hiddenArea_eval : hiddenArea = 182 := by
  simp [hiddenArea]

@[simp] def exposedArea : ℕ := separateArea - hiddenArea


 theorem amc12a_2020_p7_exposed :
    exposedArea = 658 := by
  simp [exposedArea, separateArea, hiddenArea]

end AMC12A_2020_P7


namespace AMC12A_2020_P7


@[simp] def sixFacesPerCube : ℕ := 6
@[simp] def twoFacesPerInterface : ℕ := 2


@[simp] def separateArea_geo : ℕ := sixFacesPerCube * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2 + 7^2)
@[simp] def hiddenArea_geo   : ℕ := twoFacesPerInterface * (1^2 + 2^2 + 3^2 + 4^2 + 5^2 + 6^2)

lemma separateArea_geo_eq : separateArea_geo = separateArea := rfl
lemma hiddenArea_geo_eq   : hiddenArea_geo = hiddenArea := rfl


 theorem exposed_surface_area_of_stacked_cubes :
    separateArea - hiddenArea = 658 := by
  simpa using amc12a_2020_p7

end AMC12A_2020_P7
