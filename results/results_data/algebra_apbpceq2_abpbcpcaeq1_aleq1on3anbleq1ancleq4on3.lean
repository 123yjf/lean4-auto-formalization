import Mathlib.Data.Real.Basic
import Mathlib.Tactic




noncomputable section

variables {a b c : ℝ}


lemma bc_eq (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    b*c = (1 - a)^2 := by
  have hbcsum : b + c = 2 - a := by linarith
  calc
    b*c = 1 - a*b - c*a := by linarith [hp]
    _   = 1 - a*(b + c) := by ring
    _   = 1 - a*(2 - a) := by simpa [hbcsum]
    _   = (1 - a)^2 := by ring


lemma disc_eq_a (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    a*(4 - 3*a) = (b - c)^2 := by
  have hbcsum : b + c = 2 - a := by linarith [hsum]
  have hbc : b*c = (1 - a)^2 := bc_eq (a:=a) (b:=b) (c:=c) hsum hp
  calc
    a*(4 - 3*a) = (2 - a)^2 - 4*(1 - a)^2 := by ring
    _           = (2 - a)^2 - 4*(b*c)      := by simpa [hbc]
    _           = (b + c)^2 - 4*(b*c)      := by simpa [hbcsum]
    _           = (b - c)^2                 := by ring

lemma disc_nonneg_a (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    0 ≤ a*(4 - 3*a) := by
  simpa [disc_eq_a (a:=a) (b:=b) (c:=c) hsum hp] using sq_nonneg (b - c)


lemma one_minus_a_mul_nonneg
  (hord : a ≤ b ∧ b ≤ c) (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    0 ≤ (1 - a)*(1 - 3*a) := by
  have hb : 0 ≤ b - a := sub_nonneg.mpr hord.1
  have hc : 0 ≤ c - a := sub_nonneg.mpr (le_trans hord.1 hord.2)
  have hprod : 0 ≤ (b - a)*(c - a) := mul_nonneg hb hc
  have hbcsum : b + c = 2 - a := by linarith [hsum]
  have hbc : b*c = (1 - a)^2 := bc_eq (a:=a) (b:=b) (c:=c) hsum hp
  have : (b - a)*(c - a) = (1 - a)*(1 - 3*a) := by
    calc
      (b - a)*(c - a) = b*c - a*(b + c) + a^2 := by ring
      _               = (1 - a)^2 - a*(2 - a) + a^2 := by simpa [hbc, hbcsum]
      _               = (1 - a)*(1 - 3*a) := by ring
  simpa [this] using hprod


lemma disc_eq_c (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    c*(4 - 3*c) = (a - b)^2 := by
  have habsum : a + b = 2 - c := by linarith [hsum]
  have hab : a*b = (1 - c)^2 := by
    calc
      a*b = 1 - b*c - c*a := by linarith [hp]
      _   = 1 - c*(a + b) := by ring
      _   = 1 - c*(2 - c) := by simpa [habsum]
      _   = (1 - c)^2 := by ring
  calc
    c*(4 - 3*c) = (2 - c)^2 - 4*(1 - c)^2 := by ring
    _           = (2 - c)^2 - 4*(a*b)      := by simpa [hab]
    _           = (a + b)^2 - 4*(a*b)      := by simpa [habsum]
    _           = (a - b)^2 := by ring

lemma disc_nonneg_c (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    0 ≤ c*(4 - 3*c) := by
  simpa [disc_eq_c (a:=a) (b:=b) (c:=c) hsum hp] using sq_nonneg (a - b)

lemma one_minus_c_mul_nonneg
  (hord : a ≤ b ∧ b ≤ c) (hsum : a + b + c = 2) (hp : a*b + b*c + c*a = 1) :
    0 ≤ (1 - c)*(1 - 3*c) := by
  have ha : 0 ≤ c - a := sub_nonneg.mpr (le_trans hord.1 hord.2)
  have hb : 0 ≤ c - b := sub_nonneg.mpr hord.2
  have hprod : 0 ≤ (c - a)*(c - b) := mul_nonneg ha hb
  have habsum : a + b = 2 - c := by linarith [hsum]
  have hab : a*b = (1 - c)^2 := by
    calc
      a*b = 1 - b*c - c*a := by linarith [hp]
      _   = 1 - c*(a + b) := by ring
      _   = 1 - c*(2 - c) := by simpa [habsum]
      _   = (1 - c)^2 := by ring
  have : (c - a)*(c - b) = (1 - c)*(1 - 3*c) := by
    calc
      (c - a)*(c - b) = c^2 - c*(a + b) + a*b := by ring
      _               = c^2 - c*(2 - c) + (1 - c)^2 := by simpa [habsum, hab]
      _               = (1 - c)*(1 - 3*c) := by ring
  simpa [this] using hprod


 theorem algebra_apbpceq2_abpbcpcaeq1_aleq1on3anbleq1ancleq4on3
    (h₁ : a ≤ b) (h₂ : b ≤ c)
    (hsum : a + b + c = 2)
    (hsigma : a*b + b*c + c*a = 1) :
    0 ≤ a ∧ a ≤ (1 : ℝ)/3 ∧ (1 : ℝ)/3 ≤ b ∧ b ≤ 1 ∧ 1 ≤ c ∧ c ≤ (4 : ℝ)/3 := by
  
  have hdisc_a : 0 ≤ a*(4 - 3*a) := disc_nonneg_a (a:=a) (b:=b) (c:=c) hsum hsigma
  
  have ha0 : 0 ≤ a := by
    by_contra h
    have hneg : a < 0 := lt_of_not_ge h
    have hpos : 0 < 4 - 3*a := by linarith
    have : a*(4 - 3*a) < 0 := mul_neg_of_neg_of_pos hneg hpos
    exact (not_lt_of_ge hdisc_a) this
  
  have ha_le_4d3 : a ≤ (4 : ℝ)/3 := by
    by_contra h
    have hgt : (4 : ℝ)/3 < a := lt_of_not_ge h
    have hpos : 0 < a := by linarith
    have hneg : 4 - 3*a < 0 := by linarith
    have : a*(4 - 3*a) < 0 := mul_neg_of_pos_of_neg hpos hneg
    exact (not_lt_of_ge hdisc_a) this
  
  have ha_le_2d3 : a ≤ (2 : ℝ)/3 := by
    
    have h3sum : a + a + a ≤ (2 : ℝ) := by
      have hab : a ≤ b := h₁
      have hac : a ≤ c := le_trans h₁ h₂
      have h1 : a + a ≤ a + b := add_le_add_left hab _
      have h2 : a + b + a ≤ a + b + c := add_le_add_left hac (a + b)
      have h1' : a + a + a ≤ a + b + a := by
        simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h1 a
      have h2' : a + b + a ≤ a + b + c := by
        simpa [add_comm, add_left_comm, add_assoc] using h2
      have : a + a + a ≤ a + b + c := le_trans h1' h2'
      
      have : a + a + a ≤ 2 := by linarith [this, hsum]
      simpa using this
    
    linarith
  
  have h1ma_mul_nonneg : 0 ≤ (1 - a)*(1 - 3*a) :=
    one_minus_a_mul_nonneg (a:=a) (b:=b) (c:=c) ⟨h₁, h₂⟩ hsum hsigma
  have ha_le_1d3 : a ≤ (1 : ℝ)/3 := by
    by_contra h
    have hgt : (1 : ℝ)/3 < a := lt_of_not_ge h
    have hpos : 0 < 1 - a := by linarith [ha_le_2d3]
    have hneg : 1 - 3*a < 0 := by linarith [hgt]
    have : (1 - a)*(1 - 3*a) < 0 := mul_neg_of_pos_of_neg hpos hneg
    exact (not_lt_of_ge h1ma_mul_nonneg) this
  
  have hdisc_c : 0 ≤ c*(4 - 3*c) := disc_nonneg_c (a:=a) (b:=b) (c:=c) hsum hsigma
  
  have hc_ge_2d3 : (2 : ℝ)/3 ≤ c := by
    have h2_le_3c : (2 : ℝ) ≤ c + c + c := by
      have hca : a ≤ c := le_trans h₁ h₂
      have hbc : b ≤ c := h₂
      have : a + b ≤ c + c := add_le_add hca hbc
      have : a + b + c ≤ c + c + c := add_le_add_right this c
      simpa [hsum, add_comm, add_left_comm, add_assoc] using this
    
    linarith
  
  have h1mc_mul_nonneg : 0 ≤ (1 - c)*(1 - 3*c) :=
    one_minus_c_mul_nonneg (a:=a) (b:=b) (c:=c) ⟨h₁, h₂⟩ hsum hsigma
  have hc_ge_1 : 1 ≤ c := by
    
    by_contra h
    have hlt : c < 1 := lt_of_not_ge h
    have hpos : 0 < 1 - c := by linarith
    have hneg : 1 - 3*c < 0 := by linarith [hc_ge_2d3]
    have : (1 - c)*(1 - 3*c) < 0 := mul_neg_of_pos_of_neg hpos hneg
    exact (not_lt_of_ge h1mc_mul_nonneg) this
  
  have hc_le_4d3 : c ≤ (4 : ℝ)/3 := by
    by_contra h
    have hgt : (4 : ℝ)/3 < c := lt_of_not_ge h
    have hpos : 0 < c := lt_of_lt_of_le (by norm_num) hc_ge_1
    have hneg : 4 - 3*c < 0 := by linarith
    have : c*(4 - 3*c) < 0 := mul_neg_of_pos_of_neg hpos hneg
    exact (not_lt_of_ge hdisc_c) this
  
    have two_lt_bc2 : (2 : 8) < b + c := by
      have h := add_lt_add hb_gt_one hc_gt_one
      linarith


    have : a < 0 := by
      have : 2 - (b + c) < 0 := sub_lt_zero.mpr two_lt_bc2
      simpa [hsum'] using this
  -/
  
  have hb_le_1 : b ≤ 1 := by
    linarith [hsum, ha0, hc_ge_1]


  
  have hb_ge_1d3 : (1 : ℝ)/3 ≤ b := by
    by_contra h
    have hb_lt : b < (1 : ℝ)/3 := lt_of_not_ge h
    have hab_le : a + b ≤ b + b := add_le_add_right h₁ _
    have h2b_lt' : 2*b < (2 : ℝ)/3 := by nlinarith [hb_lt]
    have h2b_lt : b + b < (2 : ℝ)/3 := by simpa [two_mul] using h2b_lt'
    have hab_lt : a + b < (2 : ℝ)/3 := lt_of_le_of_lt hab_le h2b_lt
    have hc_gt_4d3 : (4 : ℝ)/3 < c := by
      have : 2 - (a + b) > (4 : ℝ)/3 := by linarith [hab_lt]
      have hc_eq : c = 2 - (a + b) := by linarith [hsum]
      simpa [hc_eq]
    exact (not_lt_of_ge hc_le_4d3) hc_gt_4d3
  
  exact ⟨ha0, ha_le_1d3, hb_ge_1d3, hb_le_1, hc_ge_1, hc_le_4d3⟩
