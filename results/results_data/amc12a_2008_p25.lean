import Mathlib

set_option maxRecDepth 4096
set_option maxRecDepth 20000



open Complex

def amc12a_2008_p25_problem_statement : String :=
  "We have a linear recurrence on pairs (a_n, b_n) given by (a_{n+1}, b_{n+1}) = (√3 a_n − b_n, √3 b_n + a_n). Given that (a_{100}, b_{100}) = (2, 4), find the value of a₁ + b₁."



theorem amc12a_2008_p25_result :
    ((4 : ℝ) / (2 : ℝ) ^ 99) + ((-2 : ℝ) / (2 : ℝ) ^ 99)
      = (1 : ℝ) / (2 : ℝ) ^ 98 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  calc
    (4 : ℝ) / (2 : ℝ) ^ 99 + (-2) / (2 : ℝ) ^ 99

        = (4 + (-2)) / (2 : ℝ) ^ 99 := by
            simpa using (add_div (4 : ℝ) (-2) ((2 : ℝ) ^ 99)).symm
    _ = 2 / (2 : ℝ) ^ 99 := by norm_num
    _ = 2 * (1 / ((2 : ℝ) ^ 99)) := by simp [div_eq_mul_inv]
    _ = 2 * (1 / ((2 : ℝ) ^ 98 * 2)) := by simp [pow_succ]
    _ = 2 * ((1 / (2 : ℝ) ^ 98) * (1 / 2)) := by
          simpa [mul_comm, mul_left_comm, mul_assoc]
            using (one_div_mul_one_div ((2 : ℝ) ^ 98) (2 : ℝ)).symm
    _ = (2 * (1 / 2)) * (1 / (2 : ℝ) ^ 98) := by
          ac_rfl
    _ = 1 * (1 / (2 : ℝ) ^ 98) := by
          simp [h2]
    _ = 1 / (2 : ℝ) ^ 98 := by simp


lemma amc12a_2008_p25_link (z100 : ℂ) :
    (((Real.sqrt 3 : ℂ) + I) ^ 99) * (z100 / (((Real.sqrt 3 : ℂ) + I) ^ 99)) = z100 := by
  have hbase : ((Real.sqrt 3 : ℂ) + I) ≠ 0 := by
    have him : (((Real.sqrt 3 : ℂ) + I).im) = 1 := by simp
    intro h
    have h_im0 : (((Real.sqrt 3 : ℂ) + I).im) = 0 := by simpa [h]
    have h10 : (1 : ℝ) = 0 := by simpa [him] using h_im0
    exact (by norm_num : (1 : ℝ) ≠ 0) h10
  have hden : (((Real.sqrt 3 : ℂ) + I) ^ 99) ≠ 0 := by
    exact pow_ne_zero _ hbase
  field_simp [hden]


theorem amc12a_2008_p25 :
    (Complex.re ((2 + 4 * I) / (((Real.sqrt 3 : ℂ) + I) ^ 99)) +
     Complex.im ((2 + 4 * I) / (((Real.sqrt 3 : ℂ) + I) ^ 99)))
      = (1 : ℝ) / (2 : ℝ) ^ 98 := by
  
  have hsq3 : ((Real.sqrt 3 : ℝ))^2 = 3 := by
    have h : (0 : ℝ) ≤ 3 := by norm_num
    simpa [pow_two] using Real.sqrt_mul_self h
  
  have s3sqC : ( (Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) = (3 : ℂ) := by
    have hR : (Real.sqrt 3 : ℝ) * Real.sqrt 3 = 3 := by
      simpa [pow_two] using hsq3
    have hC : ((Real.sqrt 3 : ℝ) * Real.sqrt 3 : ℂ) = (3 : ℂ) := by
      exact_mod_cast hR
    simpa [Complex.ofReal_mul] using hC
    
  have hcube : ((Real.sqrt 3 : ℂ) + I) ^ 3 = (8 : ℂ) * I := by
    
    have : ((Real.sqrt 3 : ℂ) + I) ^ 3
        = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * I ^ 2 + I ^ 3 := by
      ring
    
    have hI2 : I ^ 2 = (-1 : ℂ) := by simpa [sq] using Complex.I_sq
    have hI3 : I ^ 3 = -I := by simpa using Complex.I_pow_three
    have : ((Real.sqrt 3 : ℂ) + I) ^ 3
        = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * (-1) + (-I) := by
      simpa [hI2, hI3] using this
    
    have hs3 : (Real.sqrt 3 : ℂ) ^ 3 = (3 : ℂ) * (Real.sqrt 3 : ℂ) := by
      
      calc
        (Real.sqrt 3 : ℂ) ^ 3 = (Real.sqrt 3 : ℂ) ^ 2 * (Real.sqrt 3 : ℂ) := by
          simp [pow_succ]
        _ = ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (Real.sqrt 3 : ℂ) := by
          simp [pow_two]
        _ = (3 : ℂ) * (Real.sqrt 3 : ℂ) := by
          simpa [s3sqC, mul_assoc]
    
    calc
      ((Real.sqrt 3 : ℂ) + I) ^ 3
          = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * (-1) + (-I) := by
                simpa [hI2, hI3] using this
      _ = (3 : ℂ) * (Real.sqrt 3 : ℂ) + 3 * (3 : ℂ) * I - 3 * (Real.sqrt 3 : ℂ) - I := by
                simpa [hs3, pow_two, s3sqC, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      _ = (0 : ℂ) + 8 * I := by ring
      _ = (8 : ℂ) * I := by simp
  
  have hpow : ((Real.sqrt 3 : ℂ) + I) ^ 99 = ((2 : ℂ) ^ 99) * I := by
    let z : ℂ := (Real.sqrt 3 : ℂ) + I
    have hcube' : z ^ 3 = (8 : ℂ) * I := by simpa [z] using hcube
    have hpowI : z ^ 99 = ((8 : ℂ) * I) ^ 33 := by
      have h99' : 3 * 33 = 99 := by norm_num
      calc
        z ^ 99 = z ^ (3 * 33) := by simpa [h99']
        _ = (z ^ 3) ^ 33 := by
          simpa using (pow_mul z 3 33)
        _ = ((8 : ℂ) * I) ^ 33 := by simpa [hcube']
    have hIpow : I ^ 33 = I := by simpa using (Complex.I_pow_eq_pow_mod 33)
    have h8pow : (8 : ℂ) ^ 33 = (2 : ℂ) ^ 99 := by
      have : ((2 : ℂ) ^ 3) ^ 33 = (2 : ℂ) ^ (3 * 33) := by
        simpa using (pow_mul (2 : ℂ) 3 33).symm
      have h8 : (8 : ℂ) = (2 : ℂ) ^ 3 := by norm_num
      have h99'' : 3 * 33 = 99 := by norm_num
      simpa [h8, h99''] using this
    calc
      ((Real.sqrt 3 : ℂ) + I) ^ 99 = z ^ 99 := by rfl
      _ = ((8 : ℂ) * I) ^ 33 := hpowI
      _ = (8 : ℂ) ^ 33 * (I ^ 33) := by simpa [mul_pow]
      _ = (2 : ℂ) ^ 99 * I := by simpa [h8pow, hIpow]
  
  set z1 : ℂ := (2 + 4 * I) / (((Real.sqrt 3 : ℂ) + I) ^ 99) with hz1def
  change Complex.re z1 + Complex.im z1 = (1 : ℝ) / (2 : ℝ) ^ 98
  
  have hinv : (1 / (((Real.sqrt 3 : ℂ) + I) ^ 99)) = ((-I) / ((2 : ℂ) ^ 99)) := by
    have h2cnz : ((2 : ℂ) ^ 99) ≠ 0 := by
      simpa using (pow_ne_zero 99 (by norm_num : (2 : ℂ) ≠ 0))
    have hI : (I : ℂ) ≠ 0 := by simp
    have hI2' : I ^ 2 = (-1 : ℂ) := by simpa [sq] using Complex.I_sq
    have : (1 / (((2 : ℂ) ^ 99) * I)) = ((-I) / ((2 : ℂ) ^ 99)) := by
      field_simp [h2cnz, hI]; simp [hI2']
    simpa [hpow] using this
  have hz1 : z1 = (4 - 2 * I) / ((2 : ℂ) ^ 99) := by
    have hprod : (2 + 4 * I) * (-I) = 4 - 2 * I := by
      have hI2mul : I * I = (-1 : ℂ) := by simpa using Complex.I_mul_I
      calc
        (2 + 4 * I) * (-I) = -(2 * I) + -(4 * (I * I)) := by ring
        _ = -(2 * I) + -(4 * (-1)) := by simpa [hI2mul]
        _ = -(2 * I) + 4 := by simp
        _ = 4 - 2 * I := by ring
    calc
      z1 = (2 + 4 * I) * (1 / (((Real.sqrt 3 : ℂ) + I) ^ 99)) := by
        simpa [hz1def, div_eq_mul_inv]
      _ = (2 + 4 * I) * ((-I) / ((2 : ℂ) ^ 99)) := by
        simpa [hinv]
      _ = ((2 + 4 * I) * (-I)) / ((2 : ℂ) ^ 99) := by
        simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      _ = (4 - 2 * I) / ((2 : ℂ) ^ 99) := by
        simpa [hprod]
  have hs : z1.re + z1.im = ((4 : ℝ) - 2) / (2 : ℝ) ^ 99 := by
    set r : ℝ := (2 : ℝ) ^ 99
    have hdenC : ((2 : ℂ) ^ 99) = Complex.ofReal r := by
      simpa [r, Complex.ofReal_pow]
    have hz1' : z1 = (Complex.ofReal 4 + Complex.ofReal (-2) * I) * Complex.ofReal (r⁻¹) := by
      calc
        z1 = (4 - 2 * I) / ((2 : ℂ) ^ 99) := by simpa [hz1]
        _ = (Complex.ofReal 4 + Complex.ofReal (-2) * I) / Complex.ofReal r := by
          simpa [sub_eq_add_neg, hdenC]
        _ = (Complex.ofReal 4 + Complex.ofReal (-2) * I) * (Complex.ofReal r)⁻¹ := by
          simp [div_eq_mul_inv]
        _ = (Complex.ofReal 4 + Complex.ofReal (-2) * I) * Complex.ofReal (r⁻¹) := by
          simp
    have hre : z1.re = (4 : ℝ) * r⁻¹ := by
      have := congrArg Complex.re hz1'
      simpa [Complex.mul_re]
    have him : z1.im = (-2 : ℝ) * r⁻¹ := by
      have := congrArg Complex.im hz1'
      simpa [Complex.mul_im]
    calc
      z1.re + z1.im = 4 * r⁻¹ + (-2) * r⁻¹ := by simpa [hre, him]
      _ = (4 + (-2)) * r⁻¹ := by ring
      _ = ((4 : ℝ) - 2) / r := by simpa [sub_eq_add_neg, div_eq_mul_inv]
      _ = ((4 : ℝ) - 2) / (2 : ℝ) ^ 99 := by simpa [r]
  have : ((4 : ℝ) - 2) / (2 : ℝ) ^ 99 = (1 : ℝ) / (2 : ℝ) ^ 98 := by
    have h2nz : ((2 : ℝ) ^ 99) ≠ 0 := by exact pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)
    field_simp [pow_succ, h2nz]; ring
  simpa [hs]









noncomputable section

def amc12a_2008_p25_z1 : ℂ :=
  (2 + 4 * I) / (((Real.sqrt 3 : ℂ) + I) ^ 99)


lemma amc12a_2008_p25_z1_sum :
    Complex.re amc12a_2008_p25_z1 + Complex.im amc12a_2008_p25_z1
      = (1 : ℝ) / (2 : ℝ) ^ 98 := by
  simpa [amc12a_2008_p25_z1] using amc12a_2008_p25



lemma geom_rec (α : ℂ) (z : ℕ → ℂ)
    (hrec : ∀ n, z (n+1) = α * z n) : ∀ m, z (m+1) = α^m * z 1 := by
  intro m
  induction' m with m ih
  · simp
  · have h := hrec (m+1)
    calc
      z (m+2) = α * z (m+1) := by simpa using h
      _ = α * (α^m * z 1) := by simpa [ih]
      _ = α ^ m * (α * z 1) := by simp [mul_comm, mul_left_comm, mul_assoc]
      _ = α^(m+1) * z 1 := by simp [pow_succ, mul_assoc]


lemma pow99_id : ((Real.sqrt 3 : ℂ) + I) ^ 99 = (2 : ℂ) ^ 99 * I := by
  
  have hsq3 : ((Real.sqrt 3 : ℝ))^2 = 3 := by
    have h : (0 : ℝ) ≤ 3 := by norm_num
    simpa [pow_two] using Real.sqrt_mul_self h
  have s3sqC : ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) = (3 : ℂ) := by
    have hR : (Real.sqrt 3 : ℝ) * Real.sqrt 3 = 3 := by
      simpa [pow_two] using hsq3
    have hC : ((Real.sqrt 3 : ℝ) * Real.sqrt 3 : ℂ) = (3 : ℂ) := by exact_mod_cast hR
    simpa [Complex.ofReal_mul] using hC
  have hI2 : I ^ 2 = (-1 : ℂ) := by simpa [sq] using Complex.I_sq
  have hI3 : I ^ 3 = -I := by simpa using Complex.I_pow_three
  have hs3 : (Real.sqrt 3 : ℂ) ^ 3 = (3 : ℂ) * (Real.sqrt 3 : ℂ) := by
    calc
      (Real.sqrt 3 : ℂ) ^ 3 = (Real.sqrt 3 : ℂ) ^ 2 * (Real.sqrt 3 : ℂ) := by simp [pow_succ]
      _ = ((Real.sqrt 3 : ℂ) * (Real.sqrt 3 : ℂ)) * (Real.sqrt 3 : ℂ) := by simp [pow_two]
      _ = (3 : ℂ) * (Real.sqrt 3 : ℂ) := by simpa [s3sqC, mul_assoc]
  have hcube : ((Real.sqrt 3 : ℂ) + I) ^ 3 = (8 : ℂ) * I := by
    have : ((Real.sqrt 3 : ℂ) + I) ^ 3
        = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * I ^ 2 + I ^ 3 := by
      ring
    have : ((Real.sqrt 3 : ℂ) + I) ^ 3
        = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * (-1) + (-I) := by
      simpa [hI2, hI3] using this
    calc
      ((Real.sqrt 3 : ℂ) + I) ^ 3
          = (Real.sqrt 3 : ℂ) ^ 3 + 3 * (Real.sqrt 3 : ℂ) ^ 2 * I + 3 * (Real.sqrt 3 : ℂ) * (-1) + (-I) := by
            simpa [hI2, hI3] using this
      _ = (3 : ℂ) * (Real.sqrt 3 : ℂ) + 3 * (3 : ℂ) * I - 3 * (Real.sqrt 3 : ℂ) - I := by
            simpa [hs3, pow_two, s3sqC, mul_assoc, mul_left_comm, mul_comm, sub_eq_add_neg]
      _ = 8 * I := by ring
  
  let z : ℂ := (Real.sqrt 3 : ℂ) + I
  have h99' : 99 = 3 * 33 := by norm_num
  have hcube' : z ^ 3 = (8 : ℂ) * I := by simpa [z] using hcube

  calc
    ((Real.sqrt 3 : ℂ) + I) ^ 99 = z ^ 99 := by rfl
    _ = z ^ (3 * 33) := by simpa [h99']
    _ = (z ^ 3) ^ 33 := by simpa using (pow_mul z 3 33)
    _ = ((8 : ℂ) * I) ^ 33 := by simpa [hcube']
    _ = (8 : ℂ) ^ 33 * (I ^ 33) := by simpa [mul_pow]
    _ = (2 : ℂ) ^ 99 * I := by
      have h8 : (8 : ℂ) ^ 33 = (2 : ℂ) ^ 99 := by
        have : ((2 : ℂ) ^ 3) ^ 33 = (2 : ℂ) ^ (3 * 33) := by
          simpa using (pow_mul (2 : ℂ) 3 33).symm
        have h8' : (8 : ℂ) = (2 : ℂ) ^ 3 := by norm_num
        have h99'' : 3 * 33 = 99 := by norm_num
        simpa [h8', h99''] using this
      have hI : (I : ℂ) ^ 33 = I := by simpa using (Complex.I_pow_eq_pow_mod 33)
      simpa [h8, hI]



lemma amc12a_2008_p25_from_recurrence
    (z : ℕ → ℂ)
    (hrec : ∀ n, z (n+1) = ((Real.sqrt 3 : ℂ) + I) * z n)
    (hz100 : z 100 = (2 : ℂ) + 4 * I) :
    Complex.re (z 1) + Complex.im (z 1) = (1 : ℝ) / (2 : ℝ) ^ 98 := by
  let α : ℂ := (Real.sqrt 3 : ℂ) + I
  have hstep := geom_rec α z (by simpa [α] using hrec)
  have hz100' : z 100 = α ^ 99 * z 1 := by
    simpa [α] using hstep 99
  
  have him0 : (((Real.sqrt 3 : ℂ) + I).im) = 1 := by simp
  have him : (α.im) = 1 := by simpa [α] using him0
  have hαnz : α ≠ 0 := by
    intro h
    have : α.im = 0 := by simpa [h]
    have h10 : (1 : ℝ) = 0 := by simpa [him] using this
    exact one_ne_zero h10
  have hden : (α ^ 99) ≠ 0 := by simpa using pow_ne_zero 99 hαnz
  
  have hz1L : (α ^ 99)⁻¹ * z 100 = z 1 := by
    have hcong := congrArg (fun w => (α ^ 99)⁻¹ * w) hz100'
    
    simpa [mul_assoc, hden] using hcong
  have hz1 : z 1 = (α ^ 99)⁻¹ * z 100 := by
    simpa [mul_comm] using hz1L.symm
  
  have hz1' : z 1 = (2 + 4 * I) / (α ^ 99) := by
    simpa [hz100, div_eq_mul_inv, mul_comm] using hz1
  simpa [hz1', α] using amc12a_2008_p25


lemma amc12a_2008_p25_problem_restate
    (a b : ℕ → ℝ)
    (hA : ∀ n, a (n+1) = Real.sqrt 3 * a n - b n)
    (hB : ∀ n, b (n+1) = Real.sqrt 3 * b n + a n)
    (ha100 : a 100 = 2) (hb100 : b 100 = 4) :
    a 1 + b 1 = (1 : ℝ) / (2 : ℝ) ^ 98 := by
  
  let z : ℕ → ℂ := fun n => (a n : ℂ) + (b n : ℂ) * I
  
  have hrec : ∀ n, z (n+1) = ((Real.sqrt 3 : ℂ) + I) * z n := by
    intro n
    apply Complex.ext <;>
      simp [z, hA n, hB n, Complex.mul_re, Complex.mul_im, mul_add, add_mul,
            sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  
  have hz100 : z 100 = (2 : ℂ) + 4 * I := by
    simp [z, ha100, hb100]
  
  have := amc12a_2008_p25_from_recurrence z hrec hz100
  simpa [z] using this



end
