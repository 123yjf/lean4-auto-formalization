import Mathlib.Tactic


@[simp] def coneVolume (B h : ℚ) : ℚ := (1 : ℚ) / 3 * B * h


theorem mathd_algebra_478 : coneVolume 30 (13 / 2) = 65 := by
  norm_num
