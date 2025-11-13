import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


namespace AMC12A_2021_P19

open Real
noncomputable section



def LHS (x : ℝ) : ℝ := Real.sin ((Real.pi / 2) * Real.cos x)
def RHS (x : ℝ) : ℝ := Real.cos ((Real.pi / 2) * Real.sin x)


lemma solution_zero : LHS 0 = RHS 0 := by
  simp [LHS, RHS]


lemma solution_pi_div_two : LHS (Real.pi / 2) = RHS (Real.pi / 2) := by
  simp [LHS, RHS]

open Set


private lemma mul_mem_Icc_of_abs_le_one {a y : ℝ}
    (ha : 0 ≤ a) (hy : |y| ≤ 1) : a * y ∈ Icc (-a) a := by
  have h : -1 ≤ y ∧ y ≤ 1 := by simpa [abs_le] using hy
  have hL : a * (-1 : ℝ) ≤ a * y := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h.1 ha
  have hU : a * y ≤ a * (1 : ℝ) := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left h.2 ha
  exact ⟨by simpa using hL, by simpa using hU⟩


lemma argA_mem_Icc (x : ℝ) :
    (Real.pi / 2) * Real.cos x ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  have hpos : 0 ≤ Real.pi / 2 := (half_pos Real.pi_pos).le
  have habs : |Real.cos x| ≤ 1 := by simpa using Real.abs_cos_le_one x
  simpa using mul_mem_Icc_of_abs_le_one hpos habs


lemma argB_mem_Icc_of_mem {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    (Real.pi / 2) * (1 - Real.sin x) ∈ Icc 0 (Real.pi / 2) := by
  have hpos : 0 ≤ Real.pi / 2 := (half_pos Real.pi_pos).le
  have hsin0 : 0 ≤ Real.sin x := Real.sin_nonneg_of_mem_Icc hx
  have hsin1 : Real.sin x ≤ 1 := by simpa using Real.sin_le_one x
  have h0 : 0 ≤ 1 - Real.sin x := sub_nonneg.mpr hsin1
  have h1 : 1 - Real.sin x ≤ 1 := by linarith
  refine ⟨?_, ?_⟩
  · simpa using mul_nonneg hpos h0
  · simpa [mul_comm] using mul_le_mul_of_nonneg_left h1 hpos


lemma rhs_as_sin (x : ℝ) :
    RHS x = Real.sin (Real.pi / 2 - (Real.pi / 2) * Real.sin x) := by
  have : Real.sin (Real.pi / 2 - (Real.pi / 2) * Real.sin x)
        = Real.cos ((Real.pi / 2) * Real.sin x) := by
    
    simpa [Real.sin_sub, Real.sin_pi_div_two, Real.cos_pi_div_two]
  simpa [RHS] using this.symm



lemma solutions_in_Icc {x : ℝ} (hx : x ∈ Icc 0 Real.pi) :
    LHS x = RHS x ↔ x = 0 ∨ x = Real.pi / 2 := by
  constructor
  · intro h
    
    have h1 : Real.sin ((Real.pi / 2) * Real.cos x)
              = Real.sin (Real.pi / 2 - (Real.pi / 2) * Real.sin x) := by
      simpa [LHS] using h.trans (rhs_as_sin x)
    have hfac : Real.pi / 2 - (Real.pi / 2) * Real.sin x
                = (Real.pi / 2) * (1 - Real.sin x) := by ring
    have hEqSin : Real.sin ((Real.pi / 2) * Real.cos x)
                = Real.sin ((Real.pi / 2) * (1 - Real.sin x)) := by
      simpa [hfac] using h1
    have hA := argA_mem_Icc x
    have hB0 := argB_mem_Icc_of_mem hx
    have hB : (Real.pi / 2) * (1 - Real.sin x) ∈ Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      have hneg_le : -(Real.pi / 2) ≤ 0 := by
        simpa using (neg_nonpos.mpr ((half_pos Real.pi_pos).le))
      exact ⟨le_trans hneg_le hB0.left, hB0.right⟩
    have sin_mono : StrictMonoOn Real.sin (Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
      simpa using Real.strictMonoOn_sin
    have hargs : (Real.pi / 2) * Real.cos x = (Real.pi / 2) * (1 - Real.sin x) :=
      (sin_mono.injOn hA hB) hEqSin
    have hne : (Real.pi / 2) ≠ 0 := by exact ne_of_gt (half_pos Real.pi_pos)
    have hsum' : Real.cos x = 1 - Real.sin x := by
      exact (mul_left_cancel₀ hne) (by simpa [sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, mul_assoc] using hargs)
    have hsum : Real.sin x + Real.cos x = 1 := by
      simpa [hsum', add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
    
    have hsq : (Real.sin x + Real.cos x) ^ 2 = (1 : ℝ) := by simpa [hsum]
    have hexp : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 + 2 * (Real.cos x * Real.sin x) = 1 := by
      have h := hsq
      ring_nf at h
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] using h
    have hid : (Real.sin x) ^ 2 + (Real.cos x) ^ 2 = 1 := by
      simpa [pow_two] using Real.sin_sq_add_cos_sq x
    have h2 : 2 * (Real.cos x * Real.sin x) = 0 := by
      linarith
    have hsc0 : Real.sin x = 0 ∨ Real.cos x = 0 := by
      
      have h2' : (2 * Real.sin x) * Real.cos x = 0 := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using h2
      rcases mul_eq_zero.mp h2' with h2s | h2c
      · left
        have htwo : (2 : ℝ) ≠ 0 := by norm_num
        exact (mul_eq_zero.mp h2s).resolve_left htwo
      · right
        exact h2c
    
    have hcos_anti : StrictAntiOn Real.cos (Icc 0 Real.pi) := by
      simpa using Real.strictAntiOn_cos
    have h0mem : (0 : ℝ) ∈ Icc 0 Real.pi := ⟨le_rfl, (Real.pi_pos).le⟩
    have hhalfm : Real.pi / 2 ∈ Icc 0 Real.pi :=
      ⟨(half_pos Real.pi_pos).le, (half_le_self (Real.pi_pos.le))⟩
    rcases hsc0 with hsin0 | hcos0
    · 
      have hcos1 : Real.cos x = 1 := by simpa [hsum', hsin0]
      have hceq : Real.cos x = Real.cos 0 := by simpa [Real.cos_zero] using hcos1
      have hx0' : x = 0 := (hcos_anti.injOn hx h0mem) hceq
      exact Or.inl hx0'
    · 
      have hceq : Real.cos x = Real.cos (Real.pi / 2) := by simpa [Real.cos_pi_div_two] using hcos0
      have hxhalf : x = Real.pi / 2 := (hcos_anti.injOn hx hhalfm) hceq
      exact Or.inr hxhalf
  · intro hx'
    rcases hx' with rfl | rfl
    · simpa [LHS, RHS]
    · simpa [LHS, RHS]


open Classical


lemma solution_set_eq :
    {x : ℝ | x ∈ Icc 0 Real.pi ∧ LHS x = RHS x} = ({0, Real.pi / 2} : Set ℝ) := by
  ext x; constructor
  · intro hx
    have : x = 0 ∨ x = Real.pi / 2 := (solutions_in_Icc hx.1).1 hx.2
    classical
    simpa using this
  · intro hx
    classical
    have : x = 0 ∨ x = Real.pi / 2 := by simpa using hx
    rcases this with rfl | rfl
    · exact ⟨⟨le_rfl, Real.pi_pos.le⟩, by simpa [LHS, RHS]⟩
    · exact ⟨⟨(half_pos Real.pi_pos).le, (half_le_self (Real.pi_pos.le))⟩, by simpa [LHS, RHS]⟩



lemma solutions_ncard :
    ({x : ℝ | x ∈ Icc 0 Real.pi ∧ LHS x = RHS x}).ncard = 2 := by
  classical
  have hset : {x : ℝ | x ∈ Icc 0 Real.pi ∧ LHS x = RHS x}
      = ({0, Real.pi / 2} : Set ℝ) := solution_set_eq
  have hne : (0 : ℝ) ≠ Real.pi / 2 := (ne_of_gt (half_pos Real.pi_pos)).symm
  have hn : ({x : ℝ | x ∈ Icc 0 Real.pi ∧ LHS x = RHS x}).ncard
      = (({0, Real.pi / 2} : Set ℝ)).ncard := by
    simpa using congrArg (fun s : Set ℝ => Set.ncard s) hset
  have hpair : (({0, Real.pi / 2} : Set ℝ)).ncard = 2 := Set.ncard_pair hne
  exact hn.trans hpair

end

end AMC12A_2021_P19
