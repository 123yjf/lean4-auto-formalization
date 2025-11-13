import Mathlib

open Real Complex Polynomial

noncomputable section



def r1 : ℝ := Real.cos (2 * Real.pi / 7)

def r2 : ℝ := Real.cos (4 * Real.pi / 7)

def r3 : ℝ := Real.cos (6 * Real.pi / 7)


@[simp] def S1 : ℝ := r1 + r2 + r3
@[simp] def S2 : ℝ := r1*r2 + r2*r3 + r3*r1
@[simp] def S3 : ℝ := r1*r2*r3


@[simp] def a : ℝ := -S1
@[simp] def b : ℝ := S2
@[simp] def c : ℝ := -S3


@[simp] def abc : ℝ := a * b * c


def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)


def r1C : ℂ := (zeta + zeta⁻¹) / 2
def r2C : ℂ := (zeta^2 + (zeta^2)⁻¹) / 2
def r3C : ℂ := (zeta^3 + (zeta^3)⁻¹) / 2


def S3C : ℂ := ((zeta + zeta⁻¹) * (zeta^2 + (zeta^2)⁻¹) * (zeta^3 + (zeta^3)⁻¹)) / 8



@[simp] def P : Polynomial ℝ :=
  X^3 + C a * X^2 + C b * X + C c


lemma abc_eq_symm_prod : abc = S1 * S2 * S3 := by
  unfold abc a b c S1 S2 S3
  ring


lemma abc_eq_S1S2S3 {S1 S2 S3 a b c : ℝ}
    (ha : a = -S1) (hb : b = S2) (hc : c = -S3) :
    a * b * c = S1 * S2 * S3 := by
  calc
    a * b * c = (-S1) * S2 * (-S3) := by simpa [ha, hb, hc]
    _ = ((-S1) * (-S3)) * S2 := by ac_rfl
    _ = (S1 * S3) * S2 := by
      simpa using congrArg (fun t => t * S2) (neg_mul_neg S1 S3)
    _ = S1 * S2 * S3 := by ac_rfl


lemma S1S2S3_is_1_over_32
    {S1 S2 S3 : ℝ}
    (h1 : S1 = - (1/2)) (h2 : S2 = - (1/2)) (h3 : S3 = 1/8) :
    S1 * S2 * S3 = 1/32 := by
  have : (-(1/2) : ℝ) * (-(1/2)) * (1/8) = 1/32 := by norm_num
  simpa [h1, h2, h3] using this


@[simp] def product_of_coefficients_statement : Prop :=
  let S1 := r1 + r2 + r3
  let S2 := r1*r2 + r2*r3 + r3*r1
  let S3 := r1*r2*r3
  let a := -S1; let b := S2; let c := -S3
  a * b * c = (1 : ℝ) / 32


@[simp] def amc12a_2021_p22_problem : Prop :=
  ∃ a b c : ℝ,
    let P : Polynomial ℝ := X^3 + C a * X^2 + C b * X + C c
    IsRoot P r1 ∧ IsRoot P r2 ∧ IsRoot P r3 ∧ a * b * c = (1 : ℝ) / 32
