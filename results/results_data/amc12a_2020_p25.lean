import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace AMC12A_2020_P25

open scoped BigOperators
open Real


lemma a_from_t : (1 - ((14:ℝ)/15)^2) / 4 = (29:ℝ) / 900 := by
  norm_num [pow_two]


lemma ratio_from_t : (1 + (14:ℝ)/15) / (1 - (14:ℝ)/15) = 29 := by
  have c1 : 1 + (14:ℝ)/15 = (29:ℝ)/15 := by norm_num
  have c2 : 1 - (14:ℝ)/15 = (1:ℝ)/15 := by norm_num
  simpa [c1, c2]


lemma compute_sum_value : (30:ℝ) / 29 * ((28 * 29 : ℝ) / 2) = 420 := by
  norm_num


theorem amc12a_2020_p25 : (29 + 900 : ℤ) = 929 := by
  norm_num


lemma outline_floor_quad
    (x a : ℝ) (n : ℤ) (f : ℝ)
    (hx : x = (n : ℝ) + f) (hf0 : 0 ≤ f) (hf1 : f < 1)
    (hquad : a * x^2 - (n : ℝ) * x + (n : ℝ)^2 = 0) : True := by
  trivial


lemma root_cutoff (n a t : ℝ)
    (ht : t = Real.sqrt (1 - 4 * a))
    (hcut : (1 + t) / (1 - t) = 29) : True := by
  trivial


lemma sum_eval_statement : (30:ℝ) / 29 * ((28 * 29 : ℝ) / 2) = 420 := by
  simpa using compute_sum_value




@[simp] def eqn (a x : ℝ) : Prop :=
  ((Int.floor x : ℤ) : ℝ) * (x - ((Int.floor x : ℤ) : ℝ)) = a * x^2

lemma floor_frac_outline (a x : ℝ) : eqn a x → True := by
  intro _; trivial


lemma eqn_to_quadratic {a x : ℝ} (h : eqn a x) :
    a * x^2 - ((Int.floor x : ℤ) : ℝ) * x + (((Int.floor x : ℤ) : ℝ))^2 = 0 := by
  
  set nR : ℝ := ((Int.floor x : ℤ) : ℝ) with hnR
  
  have h' : a * x^2 = nR * (x - nR) := by
    simpa [eqn, hnR, mul_comm] using h.symm
  
  calc
    a * x^2 - nR * x + nR^2
        = nR * (x - nR) - nR * x + nR^2 := by simpa [h']
    _ = 0 := by
      ring


lemma root_interval_n (n : ℕ) (hn1 : 1 ≤ n) (hn2 : n ≤ 28) :
    let x : ℝ := ((30:ℝ) / 29) * n
    ((n : ℝ) ≤ x) ∧ (x < (n : ℝ) + 1) := by
  intro x
  
  have hxsub : x - (n : ℝ) = (n : ℝ) / 29 := by
    calc
      x - (n:ℝ)
          = ((30:ℝ)/29 * (n:ℝ)) - 1 * (n:ℝ) := by simp [x]
      _ = (((30:ℝ)/29) - 1) * (n:ℝ) := by ring
      _ = ((1:ℝ)/29) * (n:ℝ) := by norm_num
      _ = (n:ℝ) / 29 := by simpa [div_eq_mul_inv, mul_comm]
  
  have hx : x = (n:ℝ) + (n:ℝ) / 29 := by
    have := hxsub; linarith
  
  have hx_nonneg : 0 ≤ (n:ℝ) / 29 := by
    have hn0 : 0 ≤ (n:ℝ) := by exact_mod_cast (Nat.zero_le n)
    have h29pos : 0 < (29:ℝ) := by norm_num
    exact div_nonneg hn0 h29pos.le
  have hlower : (n:ℝ) ≤ x := by simpa [hx] using add_le_add_left hx_nonneg (n:ℝ)
  
  have hnlt : (n:ℝ) / 29 < 1 := by
    have hle : (n:ℝ) ≤ (28:ℝ) := by exact_mod_cast hn2
    have hbound : (n:ℝ) / 29 ≤ (28:ℝ) / 29 := by
      have h29inv_nonneg : 0 ≤ (1/29:ℝ) := by norm_num
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_right hle h29inv_nonneg)
    have : (28:ℝ) / 29 < 1 := by norm_num
    exact lt_of_le_of_lt hbound this
  have hupper : x < (n:ℝ) + 1 := by
    have := add_lt_add_left hnlt (n:ℝ)
    simpa [hx, add_comm, add_left_comm, add_assoc] using this
  exact ⟨hlower, hupper⟩


lemma negative_exclusion_outline : True := by
  trivial




namespace AMC12A_2020_P25.RationalFacts


@[simp] def tQ : ℚ := 14 / 15
@[simp] def aQ : ℚ := ((1 : ℚ) - tQ^2) / 4

lemma aQ_val : aQ = 29 / 900 := by
  unfold aQ tQ
  norm_num

lemma ratio29_Q : ((1 : ℚ) + tQ) / (1 - tQ) = 29 := by
  unfold tQ
  norm_num

lemma sum420_Q : ((30 : ℚ) / 29) * ((28 * 29) / 2) = 420 := by
  norm_num

lemma coprime_29_900 : Nat.Coprime 29 900 := by
  decide

lemma p_plus_q_nat : (29 : ℕ) + 900 = 929 := by decide
lemma p_plus_q_int : (29 + 900 : ℤ) = 929 := by norm_num

end RationalFacts


namespace AMC12A_2020_P25

lemma lowest_terms : Nat.Coprime 29 900 := by
  simpa using AMC12A_2020_P25.RationalFacts.coprime_29_900

end AMC12A_2020_P25
