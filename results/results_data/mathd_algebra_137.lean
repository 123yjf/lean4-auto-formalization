
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section


@[simp] def fourPercentIncrease (old new : ℝ) : Prop :=
  new = ((26 : ℝ) / 25) * old




lemma old_of_eq {old : ℝ} (h : ((26 : ℝ) / 25) * old = 598) : old = 575 := by
  have h' := congrArg (fun x : ℝ => ((25 : ℝ) / 26) * x) h
  have : old = ((25 : ℝ) / 26) * 598 := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  have hval : ((25 : ℝ) / 26) * 598 = 575 := by norm_num
  simpa [hval] using this




theorem mathd_algebra_137_concrete {old : ℝ}
    (h : fourPercentIncrease old 598) : old = 575 := by
  
  have hx : ((26 : ℝ) / 25) * old = 598 := by simpa [fourPercentIncrease] using h.symm
  exact old_of_eq hx



@[simp] def thisYearEnrollment : ℝ := 598
@[simp] def lastYearEnrollment : ℝ := 575




theorem mathd_algebra_137
    (hinc : fourPercentIncrease lastYearEnrollment thisYearEnrollment)
    (hnew : thisYearEnrollment = 598) :
    lastYearEnrollment = 575 := by
  have hx : ((26 : ℝ) / 25) * lastYearEnrollment = 598 := by
    have : ((26 : ℝ) / 25) * lastYearEnrollment = thisYearEnrollment := by
      simpa [fourPercentIncrease] using hinc.symm
    simpa [thisYearEnrollment, hnew] using this
  exact old_of_eq hx
