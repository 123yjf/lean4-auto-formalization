

























import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

noncomputable section
open scoped Real
open Classical


namespace IMO1960P2


lemma sq_factor (t : ℝ) : (t^2 - 1)^2 = (t - 1)^2 * (t + 1)^2 := by
  ring

lemma one_sub_sq (t : ℝ) : (1 - t)^2 = (t - 1)^2 := by
  ring


lemma cancel_pos_sq_iff {t : ℝ} (hne : t ≠ 1) :
  ((t - 1)^2 * (t + 1)^2 < (t^2 + 8) * (t - 1)^2) ↔ ((t + 1)^2 < t^2 + 8) := by
  have hnonneg : 0 ≤ (t - 1)^2 := by exact sq_nonneg (t - 1)
  
  have dummy_true : True := trivial
  constructor
  · intro h
    have h' : (t - 1)^2 * (t + 1)^2 < (t - 1)^2 * (t^2 + 8) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using h
    have : (t + 1)^2 < t^2 + 8 := (lt_of_mul_lt_mul_left h' hnonneg)
    simpa using this
  · intro h
    have hpos2 : 0 < (t - 1)^2 := by
      have : (t - 1) ≠ 0 := sub_ne_zero.mpr hne
      simpa using (sq_pos_iff.mpr this)
    have h' := (mul_lt_mul_left hpos2).mpr h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h'


lemma cleared_equiv {t : ℝ} (hne : t ≠ 1) :
  ((t^2 - 1)^2 < (t^2 + 8) * (1 - t)^2) ↔ ((t + 1)^2 < t^2 + 8) := by
  have hA : (t^2 - 1)^2 = (t - 1)^2 * (t + 1)^2 := by ring
  have hB : (1 - t)^2 = (t - 1)^2 := by ring
  constructor
  · intro h
    have h' : (t - 1)^2 * (t + 1)^2 < (t^2 + 8) * (t - 1)^2 := by
      simpa [hA, hB, mul_comm, mul_left_comm, mul_assoc] using h
    exact (cancel_pos_sq_iff hne).1 h'
  · intro h
    have h' : (t - 1)^2 * (t + 1)^2 < (t^2 + 8) * (t - 1)^2 :=
      (cancel_pos_sq_iff hne).2 h
    simpa [hA, hB, mul_comm, mul_left_comm, mul_assoc] using h'


lemma cancel_sq_iff (t : ℝ) (h : t ≠ 1) :
  (t^2 - 1)^2 < (t^2 + 8) * (1 - t)^2 ↔ (t + 1)^2 < t^2 + 8 := by
  have hnonneg : 0 ≤ (t - 1)^2 := by exact sq_nonneg (t - 1)
  have hpos : 0 < (t - 1)^2 := by
    simpa using (sq_pos_iff.mpr (sub_ne_zero.mpr h))
  have h1 : (1 - t) = -(t - 1) := by
    ring
  have h1sq : (1 - t)^2 = (t - 1)^2 := by
    calc
      (1 - t)^2 = (-(t - 1))^2 := by
        simpa using congrArg (fun x => x^2) h1
      _ = (t - 1)^2 := by
        ring
  have hfac2 : (t^2 - 1)^2 = (t - 1)^2 * (t + 1)^2 := by
    simpa using sq_factor t
  constructor
  · intro hlt
    have h' : (t - 1)^2 * (t + 1)^2 < (t - 1)^2 * (t^2 + 8) := by
      simpa [hfac2, h1sq, mul_comm, mul_left_comm, mul_assoc] using hlt
    have : (t + 1)^2 < t^2 + 8 := (lt_of_mul_lt_mul_left h' hnonneg)
    simpa using this
  · intro hlt
    have h' := (mul_lt_mul_left hpos).mpr hlt
    simpa [hfac2, h1sq, mul_comm, mul_left_comm, mul_assoc] using h'



theorem inequality_iff {x : ℝ}
    (hdom : 0 ≤ 2*x + 1) (hne : (1 - Real.sqrt (2*x + 1)) ≠ 0) :
    4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9 ↔ x < (45 : ℝ) / 8 := by
  set t := Real.sqrt (2*x + 1) with ht
  have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.sqrt_nonneg (2*x + 1)
  have ht_sq : t^2 = 2*x + 1 := by simpa [ht] using Real.sq_sqrt hdom
  have hposd : 0 < (1 - t)^2 := by
    have : (1 - t) ≠ 0 := by simpa [ht] using hne
    simpa using (sq_pos_iff.mpr this)
  have t_ne_one : t ≠ 1 := by
    intro h1; exact hne (by simpa [ht, h1])
  constructor
  · intro hx
    have hx' : 4*x^2 < (2*x + 9) * (1 - t)^2 := by
      have := (lt_div_iff hposd).1
      simpa [ht] using this hx
    
    have hx'' : (t^2 - 1)^2 < (t^2 + 8) * (1 - t)^2 := by
      
      have h4 : 4*x^2 = (t^2 - 1)^2 := by
        have : 2*x = t^2 - 1 := by simpa [two_mul, ht_sq, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        simpa [this, pow_two] using congrArg (fun y => y^2) this
      have h29 : 2*x + 9 = t^2 + 8 := by simpa [ht_sq, add_comm, add_left_comm, add_assoc]
      simpa [h4, h29]
        using hx'
    
    have hcore : (t + 1)^2 < t^2 + 8 := by
      simpa using (IMO1960P2.cancel_sq_iff t_ne_one).1 hx''
    
    have htlt : t < (7 : ℝ) / 2 := by
      
      have : t^2 + 2*t + 1 < t^2 + 8 := by simpa [pow_two, two_mul, add_comm, add_left_comm, add_assoc]
        using hcore
      have : 2*t + 1 < 8 := by linarith
      linarith
    
    have hb : 0 ≤ (7 : ℝ) / 2 := by norm_num
    have hxsq : 2*x + 1 < ((7 : ℝ) / 2)^2 := by
      
      have : Real.sqrt (2*x + 1) < (7 : ℝ) / 2 := by simpa [ht] using htlt
      exact (Real.sqrt_lt_iff.mpr ⟨hdom, hb, this⟩)
    have : x < (45 : ℝ) / 8 := by
      
      have : 2*x < (49 : ℝ) / 4 - 1 := by simpa [pow_two] using hxsq
      have : 2*x < (45 : ℝ) / 4 := by norm_num at this; simpa using this
      have hhalf : 0 < (1/2 : ℝ) := by norm_num
      have := (mul_lt_mul_left hhalf).mpr this
      simpa [mul_comm, mul_left_comm, mul_assoc, inv_mul_eq_iff_eq_mul₀, two_mul] using this
    exact this
  · intro hxlt
    
    have hb : 0 ≤ (7 : ℝ) / 2 := by norm_num
    have hxsq : 2*x + 1 < ((7 : ℝ) / 2)^2 := by
      have : 2*x < (45 : ℝ) / 4 := by
        have : 8 * x < (45 : ℝ) := by
          have hpos8 : 0 < (8 : ℝ) := by norm_num
          exact (mul_lt_mul_left hpos8).mpr hxlt
        have : 2 * (2 * x) < (45 : ℝ) := by simpa [two_mul] using this
        have : 2*x < (45 : ℝ) / 2 :=
          (lt_of_mul_lt_mul_left this (by norm_num : (0:ℝ) ≤ (2:ℝ)))
        have : 2*x < (45 : ℝ) / 4 + (45 : ℝ) / 4 := by
          simpa [two_mul, add_comm] using this
        
        simpa [add_comm, add_left_comm, add_assoc] using this
      have : Real.sqrt (2*x + 1) < (7 : ℝ) / 2 := by
        
        exact (Real.sqrt_lt_iff.mp ?_)
      
      have : 0 ≤ 2*x + 1 ∧ 0 ≤ (7 : ℝ) / 2 ∧ 2*x + 1 < ((7 : ℝ) / 2)^2 := by
        refine ⟨hdom, hb, ?_⟩; simpa [pow_two] using this
      exact this.2.2
    
    have htlt : t < (7 : ℝ) / 2 := by
      
      have hposb : 0 ≤ (7 : ℝ) / 2 := by norm_num
      have := (Real.lt_sqrt_iff.mp ?_)
      admit
    
    admit
-/



end IMO1960P2



lemma clear_denom_strict_lt_right {A B d : ℝ} (hd : 0 < d) (h : A / d < B) :
  A < B * d := by
  have h' := (mul_lt_mul_of_pos_right h hd)
  have h'' : (A / d) * d < B * d := by simpa [mul_comm] using h'
  have hne : d ≠ 0 := ne_of_gt hd
  
  have hleft2 : d * (A / d) = (A * d) / d := by
    have hcomm : d * (A / d) = (A / d) * d := by simpa [mul_comm]
    have hdiv : (A / d) * d = (A * d) / d := by simpa [div_mul_eq_mul_div]
    exact hcomm.trans hdiv
  have hleftA : d * (A / d) = A := by
    have : (A * d) / d = A := by simpa [hne] using (mul_div_cancel A hne)
    simpa [hleft2]
  simpa [hleftA, mul_comm, mul_left_comm, mul_assoc] using h''

open IMO1960P2


lemma inequality_implies_bound {x : ℝ}
    (hdom : 0 ≤ 2*x + 1) (hne : (1 - Real.sqrt (2*x + 1)) ≠ 0)
    (hx : 4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9) :
    x < (45 : ℝ) / 8 := by
  set t := Real.sqrt (2*x + 1) with ht
  have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.sqrt_nonneg (2*x + 1)
  have ht_sq : t^2 = 2*x + 1 := by simpa [ht] using Real.sq_sqrt hdom
  have hposd : 0 < (1 - t)^2 := by
    have : (1 - t) ≠ 0 := by simpa [ht] using hne
    simpa using (sq_pos_iff.mpr this)
  
  have hx1 : 4*x^2 / (1 - t)^2 < 2*x + 9 := by simpa [ht] using hx
  
  have hx1mul : 4*x^2 < (2*x + 9) * (1 - t)^2 :=
    clear_denom_strict_lt_right hposd hx1
  
  have h4 : 4*x^2 = (t^2 - 1)^2 := by
    calc
      4*x^2 = (2*x)^2 := by ring
      _ = (t^2 - 1)^2 := by
        have : 2*x = t^2 - 1 := by linarith [ht_sq]
        simpa using congrArg (fun y => y^2) this
  have hR : 2*x + 9 = t^2 + 8 := by
    calc
      2*x + 9 = (2*x + 1) + 8 := by ring
      _ = t^2 + 8 := by simpa [ht_sq]
  have hx1mul' : 4*x^2 < (t^2 + 8) * (1 - t)^2 := by
    simpa [hR] using hx1mul
  have hx_mul : (t^2 - 1)^2 < (t^2 + 8) * (1 - t)^2 := by
    simpa [h4] using hx1mul'
  
  have hcore : (t + 1)^2 < t^2 + 8 := by
    have t_ne_one : t ≠ 1 := by
      have h1ne : (1 - t) ≠ 0 := by simpa [ht] using hne
      have : 1 ≠ t := sub_ne_zero.mp h1ne
      simpa [ne_comm] using this
    simpa using (cancel_sq_iff t t_ne_one).1 hx_mul
  
  have htlt : t < (7 : ℝ) / 2 := by
    have hsub : (t + 1)^2 - t^2 < 8 := by linarith [hcore]
    have : 2*t + 1 < 8 := by
      have hdiff : (t + 1)^2 - t^2 = 2*t + 1 := by ring
      simpa [hdiff] using hsub
    linarith
  
  have hb : 0 ≤ (7 : ℝ) / 2 := by norm_num
  have abslt : |t| < |(7 : ℝ) / 2| := by
    have htabs : |t| = t := by simpa [abs_of_nonneg ht_nonneg]
    have hbabs : |(7 : ℝ) / 2| = (7 : ℝ) / 2 := by simpa [abs_of_nonneg hb]
    simpa [htabs, hbabs] using htlt
  have hxsq : 2*x + 1 < ((7 : ℝ) / 2)^2 := by
    simpa [ht_sq] using (sq_lt_sq.mpr abslt)
  
  
  have h49 : ((7 : ℝ) / 2)^2 = (49 : ℝ) / 4 := by norm_num
  have hx1 : 2*x + 1 < (49 : ℝ) / 4 := by simpa [h49] using hxsq
  have hx2 : 2*x < (45 : ℝ) / 4 := by linarith
  have hx3 : (1/2 : ℝ) * (2*x) < (1/2 : ℝ) * ((45 : ℝ) / 4) :=
    (mul_lt_mul_left (by norm_num : 0 < (1/2 : ℝ))).mpr hx2
  have : x < (45 : ℝ) / 8 := by
    calc
      x = (1/2 : ℝ) * (2*x) := by ring
      _ < (1/2 : ℝ) * ((45 : ℝ) / 4) := hx3
      _ = (45 : ℝ) / 8 := by norm_num
  exact this







lemma bound_implies_inequality {x : ℝ}
    (hdom : 0 ≤ 2*x + 1) (hne : (1 - Real.sqrt (2*x + 1)) ≠ 0)
    (hxlt : x < (45 : ℝ) / 8) :
    4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9 := by
  set t := Real.sqrt (2*x + 1) with ht
  have ht_nonneg : 0 ≤ t := by simpa [ht] using Real.sqrt_nonneg (2*x + 1)
  have ht_sq : t^2 = 2*x + 1 := by simpa [ht] using Real.sq_sqrt hdom
  
  have hb : 0 ≤ (7 : ℝ) / 2 := by norm_num
  have hxsq49 : 2*x + 1 < (49 : ℝ) / 4 := by
    
    have hx2 : 2*x < (45 : ℝ) / 4 := by
      have hmul := (mul_lt_mul_of_pos_left hxlt (by norm_num : 0 < (2 : ℝ)))
      
      have htwice : 2 * ((45 : ℝ) / 8) = (45 : ℝ) / 4 := by norm_num
      simpa [htwice, mul_comm, mul_left_comm, mul_assoc] using hmul
    linarith
  have htlt : t < (7 : ℝ) / 2 := by
    
    have hval : ((7 : ℝ) / 2)^2 = (49 : ℝ) / 4 := by norm_num
    have hsq : t^2 < ((7 : ℝ) / 2)^2 := by
      have : 2*x + 1 < ((7 : ℝ) / 2)^2 := by simpa [hval] using hxsq49
      simpa [ht_sq] using this
    have abslt : |t| < |(7 : ℝ) / 2| := (sq_lt_sq).1 hsq
    have htabs : |t| = t := by simpa [abs_of_nonneg ht_nonneg]
    have hbabs : |(7 : ℝ) / 2| = (7 : ℝ) / 2 := by simpa [abs_of_nonneg hb]
    simpa [htabs, hbabs] using abslt
  
  have hcore : (t + 1)^2 < t^2 + 8 := by
    have : 2*t + 1 < 8 := by linarith
    have hdiff : (t + 1)^2 - t^2 = 2*t + 1 := by ring
    have : (t + 1)^2 - t^2 < 8 := by simpa [hdiff] using this
    linarith
  
  have t_ne_one : t ≠ 1 := by
    
    have h1ne : (1 - t) ≠ 0 := by simpa [ht] using hne
    exact by
      have : 1 ≠ t := sub_ne_zero.mp h1ne
      simpa [ne_comm] using this
  have hposd : 0 < (1 - t)^2 := by
    have : (1 - t) ≠ 0 := by simpa [ht] using hne
    simpa using (sq_pos_iff.mpr this)
  have hx_mul' : (t^2 - 1)^2 < (t^2 + 8) * (1 - t)^2 := by
    simpa using (cancel_sq_iff t t_ne_one).2 hcore
  
  have h4sq : (2*x)^2 = (t^2 - 1)^2 := by
    have : 2*x = t^2 - 1 := by linarith [ht_sq]
    simpa using congrArg (fun y => y^2) this
  have hR : t^2 + 8 = 2*x + 9 := by
    calc
      t^2 + 8 = (2*x + 1) + 8 := by simpa [ht_sq]
      _ = 2*x + 9 := by ring
  
  have hx_div' : (t^2 - 1)^2 / (1 - t)^2 < t^2 + 8 := by
    have hne0 : (1 - t)^2 ≠ 0 := ne_of_gt hposd
    have := div_lt_div_of_pos_right hx_mul' hposd
    
    simpa [mul_comm, mul_left_comm, mul_assoc, hne0] using this
  have hx_div : 4*x^2 / (1 - t)^2 < 2*x + 9 := by
    have hx_div'' : ((2*x)^2) / (1 - t)^2 < t^2 + 8 := by
      simpa [h4sq] using hx_div'
    
    have h2sq : (2*x)^2 = 4*x^2 := by ring
    simpa [h2sq, hR] using hx_div''
  simpa [ht] using hx_div




lemma domain_iff (x : ℝ) : 0 ≤ 2*x + 1 ↔ (-1/2 : ℝ) ≤ x := by
  constructor
  · intro h; have : 2*x ≥ -1 := by linarith
    have : x ≥ -1/2 := by linarith
    simpa using this
  · intro h; linarith


 theorem solution_set :
  {x : ℝ | 0 ≤ 2*x + 1 ∧ (1 - Real.sqrt (2*x + 1)) ≠ 0 ∧
               4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9}
  = {x : ℝ | (-1/2 : ℝ) ≤ x ∧ x ≠ 0 ∧ x < (45 : ℝ) / 8} := by
  ext x; constructor
  · intro hx
    rcases hx with ⟨hdom, hne, hineq⟩
    have hxlt : x < (45 : ℝ) / 8 := inequality_implies_bound hdom hne hineq
    
    have hxne : x ≠ 0 := by
      intro h0
      exact hne (by simpa [h0])
    
    have hxge : (-1/2 : ℝ) ≤ x := (domain_iff x).1 hdom
    exact ⟨hxge, hxne, hxlt⟩
  · intro hx
    rcases hx with ⟨hxge, hxne, hxlt⟩
    
    have hdom : 0 ≤ 2*x + 1 := (domain_iff x).2 hxge
    
    have hne : (1 - Real.sqrt (2*x + 1)) ≠ 0 := by
      intro hzero
      have hs : Real.sqrt (2*x + 1) = 1 := by
        have := sub_eq_zero.mp hzero
        simpa [eq_comm] using this.symm
      have hsq := congrArg (fun u : ℝ => u^2) hs
      have : 2*x + 1 = 1 := by simpa [Real.sq_sqrt hdom] using hsq
      have : x = 0 := by linarith
      exact hxne this
    
    have hineq : 4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9 :=
      bound_implies_inequality hdom hne hxlt
    exact ⟨hdom, hne, hineq⟩






theorem inequality_iff {x : ℝ}
    (hdom : 0 ≤ 2*x + 1) (hne : (1 - Real.sqrt (2*x + 1)) ≠ 0) :
    4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9 ↔ x < (45 : ℝ) / 8 := by
  constructor
  · intro hx; exact inequality_implies_bound hdom hne hx
  · intro hx; exact bound_implies_inequality hdom hne hx



theorem pointwise_solution_iff (x : ℝ) :
  (0 ≤ 2*x + 1 ∧ (1 - Real.sqrt (2*x + 1)) ≠ 0 ∧
     4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9)
  ↔ ((-1/2 : ℝ) ≤ x ∧ x ≠ 0 ∧ x < (45 : ℝ) / 8) := by
  
  simpa [Set.mem_setOf_eq] using
    congrArg (fun s : Set ℝ => x ∈ s) solution_set


open Set


theorem solution_set_union :
  {x : ℝ | 0 ≤ 2*x + 1 ∧ (1 - Real.sqrt (2*x + 1)) ≠ 0 ∧
               4*x^2 / (1 - Real.sqrt (2*x + 1))^2 < 2*x + 9}
  = ({x : ℝ | (-1/2 : ℝ) ≤ x ∧ x < 0}
     ∪ {x : ℝ | 0 < x ∧ x < (45 : ℝ) / 8}) := by
  classical
  ext x; constructor
  · intro hx
    have hx' : (-1/2 : ℝ) ≤ x ∧ x ≠ 0 ∧ x < (45 : ℝ) / 8 :=
      (pointwise_solution_iff x).1 hx
    rcases hx' with ⟨hxge, hxne, hxlt⟩
    by_cases hxneg : x < 0
    · exact Or.inl ⟨hxge, hxneg⟩
    · have hxge0 : 0 ≤ x := le_of_not_gt hxneg
      have hxpos : 0 < x := lt_of_le_of_ne hxge0 (Ne.symm hxne)
      exact Or.inr ⟨hxpos, hxlt⟩
  · intro hx
    rcases hx with hx | hx
    · rcases hx with ⟨hxge, hxneg⟩
      have hxne : x ≠ 0 := ne_of_lt hxneg
      have hxlt : x < (45 : ℝ) / 8 := lt_trans hxneg (by norm_num)
      exact (pointwise_solution_iff x).2 ⟨hxge, hxne, hxlt⟩
    · rcases hx with ⟨hxpos, hxlt⟩
      have hxge : (-1/2 : ℝ) ≤ x :=
        le_trans (by norm_num) (le_of_lt hxpos)
      have hxne : x ≠ 0 := ne_of_gt hxpos
      exact (pointwise_solution_iff x).2 ⟨hxge, hxne, hxlt⟩
