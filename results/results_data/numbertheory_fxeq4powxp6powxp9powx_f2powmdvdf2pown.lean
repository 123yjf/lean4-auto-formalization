import Mathlib.Data.Nat.Basic
import Mathlib.Tactic


def f (x : ℕ) : ℕ := 4 ^ x + 6 ^ x + 9 ^ x


@[simp] def fZ (x : ℕ) : ℤ := (4 : ℤ) ^ x + (6 : ℤ) ^ x + (9 : ℤ) ^ x

lemma coe_f_eq_fZ (x : ℕ) : (f x : ℤ) = fZ x := by
  simp [f, fZ]


lemma fZ_dvd_double (x : ℕ) : fZ x ∣ fZ (2 * x) := by
  
  set r : ℤ := (2 : ℤ) ^ x
  set s : ℤ := (3 : ℤ) ^ x
  
  have h4x : (4 : ℤ) ^ x = r ^ 2 := by
    have : (4 : ℤ) = (2 : ℤ) ^ 2 := by norm_num
    
    calc
      (4 : ℤ) ^ x = ((2 : ℤ) ^ 2) ^ x := by simpa [this]
      _ = (2 : ℤ) ^ (2 * x) := by simpa [pow_mul]
      _ = ((2 : ℤ) ^ x) ^ 2 := by
        simpa [pow_mul, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = r ^ 2 := by simpa [r]
  have h9x : (9 : ℤ) ^ x = s ^ 2 := by
    have : (9 : ℤ) = (3 : ℤ) ^ 2 := by norm_num
    calc
      (9 : ℤ) ^ x = ((3 : ℤ) ^ 2) ^ x := by simpa [this]
      _ = (3 : ℤ) ^ (2 * x) := by simpa [pow_mul]
      _ = ((3 : ℤ) ^ x) ^ 2 := by
        simpa [pow_mul, two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ = s ^ 2 := by simpa [s]
  have h6x : (6 : ℤ) ^ x = r * s := by
    simpa [r, s] using (mul_pow (2 : ℤ) (3 : ℤ) x)
  
  have h4_2x : (4 : ℤ) ^ (2 * x) = (r ^ 2) ^ 2 := by
    
    simpa [h4x] using (pow_mul (4 : ℤ) x 2)
  have h6_2x : (6 : ℤ) ^ (2 * x) = (r * s) ^ 2 := by
    simpa [h6x] using (pow_mul (6 : ℤ) x 2)
  have h9_2x : (9 : ℤ) ^ (2 * x) = (s ^ 2) ^ 2 := by
    simpa [h9x] using (pow_mul (9 : ℤ) x 2)
  
  have fac : (r ^ 2 + r * s + s ^ 2) * (r ^ 2 - r * s + s ^ 2)
              = (r ^ 2) ^ 2 + (r * s) ^ 2 + (s ^ 2) ^ 2 := by ring
  refine ⟨r ^ 2 - r * s + s ^ 2, ?_⟩
  
  have hx : fZ x = r ^ 2 + r * s + s ^ 2 := by
    simp [fZ, h4x, h6x, h9x, add_comm, add_left_comm, add_assoc, mul_comm]
  have h2x : fZ (2 * x) = (r ^ 2) ^ 2 + (r * s) ^ 2 + (s ^ 2) ^ 2 := by
    simp [fZ, h4_2x, h6_2x, h9_2x, mul_comm]
  simpa [hx, h2x]


lemma nat_dvd_of_int_mul_eq {a b : ℕ} {z : ℤ}
    (h : (a : ℤ) * z = (b : ℤ)) (hz : 0 ≤ z) : a ∣ b := by
  refine ⟨Int.toNat z, ?_⟩
  have hz' : (Int.ofNat (Int.toNat z)) = z := by simpa using Int.toNat_of_nonneg hz
  
  have : (Int.ofNat a) * (Int.ofNat (Int.toNat z)) = Int.ofNat b := by
    simpa [hz'] using h
  
  have : Int.ofNat (a * Int.toNat z) = Int.ofNat b := by
    simpa [Int.ofNat_mul] using this
  simpa using this


lemma f_dvd_double (x : ℕ) : f x ∣ f (2 * x) := by
  
  rcases fZ_dvd_double x with ⟨gZ, hZ⟩
  
  have : (f (2 * x) : ℤ) = (f x : ℤ) * gZ := by
    simpa [coe_f_eq_fZ] using hZ
  
  
  have hz_nonneg : 0 ≤ gZ := by
    
    
    
    have : True := trivial; exact le_of_lt (Int.lt_add_one_iff.mpr (Int.le.intro rfl))
  
  exact nat_dvd_of_int_mul_eq (by simpa using this) hz_nonneg


theorem numbertheory_fxeq4powxp6powxp9powx_f2powmdvdf2pown
    (m n : ℕ) (hmn : m ≤ n) : f (2 ^ m) ∣ f (2 ^ n) := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  
  induction k with
  | zero =>
      
      simp
  | succ k ih =>
      
      have hk : f (2 ^ (m + k)) ∣ f (2 * 2 ^ (m + k)) := f_dvd_double (2 ^ (m + k))
      
      simpa [pow_succ, two_mul, add_comm, add_left_comm, add_assoc, mul_comm]
        using ih.trans hk
