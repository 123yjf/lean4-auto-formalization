import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum



open Int




axiom quadratic_roots_constraint (a b c d k m : ℕ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h_order : a < b ∧ b < c ∧ c < d)
  (h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h_prod : a * d = b * c)
  (h_sum1 : a + d = 2^k)
  (h_sum2 : b + c = 2^m) :
  ∃ u v : ℕ, Odd u ∧ Odd v ∧
  u^2 = 2^(2*k-2) - a*d ∧
  v^2 = 2^(2*m-2) - b*c ∧
  a = 2^(k-1) - u ∧ d = 2^(k-1) + u ∧
  b = 2^(m-1) - v ∧ c = 2^(m-1) + v

axiom diophantine_constraint (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 2) (h_order : k > m) :
  ∃ p q : ℕ, p * q = 2^(2*m-4) * (2^(2*(k-m)) - 1) ∧
  (Odd p ∧ Even q ∨ Even p ∧ Odd q) ∧
  p > 2^(m-2) * (2^(k-m) - 1) ∧ q > p

axiom case_analysis_result (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 3) (h_order : k > m) :
  (∃ p q : ℕ, Odd p ∧ Even q ∧
   p = 2^(2*(k-m)) - 1 ∧ q = 2^(2*m-4) ∧
   p * q = 2^(2*m-4) * (2^(2*(k-m)) - 1) ∧
   q > p ∧ p > 2^(m-2) * (2^(k-m) - 1)) →
  k = 2*m - 2

axiom final_calculation (m : ℕ) (hm : m ≥ 3) :
  let k := 2*m - 2
  let u := 2^(2*(m-2)) - 1 + 2^(2*m-4)
  2^(k-1) - u = 1

axiom k_bound (a d k : ℕ) (h_pos : 0 < a ∧ 0 < d) (h_odd : Odd a ∧ Odd d) (h_sum : a + d = 2^k) : k ≥ 2

axiom m_bound (b c m : ℕ) (h_pos : 0 < b ∧ 0 < c) (h_odd : Odd b ∧ Odd c) (h_sum : b + c = 2^m) : m ≥ 2

axiom k_gt_m (a b c d k m : ℕ) (h_order : a < b ∧ b < c ∧ c < d) (h_sum1 : a + d = 2^k) (h_sum2 : b + c = 2^m) : k > m

axiom m_ge_3 (a b c d k m : ℕ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h_order : a < b ∧ b < c ∧ c < d)
  (h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h_prod : a * d = b * c)
  (h_sum1 : a + d = 2^k)
  (h_sum2 : b + c = 2^m) : m ≥ 3

axiom u_form (a b c d k m u v : ℕ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h_order : a < b ∧ b < c ∧ c < d)
  (h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h_prod : a * d = b * c)
  (h_sum1 : a + d = 2^k)
  (h_sum2 : b + c = 2^m)
  (h_k_eq : k = 2*m - 2)
  (hu_odd : Odd u) (hv_odd : Odd v)
  (hu_sq : u^2 = 2^(2*k-2) - a*d)
  (hv_sq : v^2 = 2^(2*m-2) - b*c)
  (ha_eq : a = 2^(k-1) - u) : u = 2^(2*(m-2)) - 1 + 2^(2*m-4)

axiom case_existence (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 3) (h_order : k > m) :
  ∃ p q : ℕ, Odd p ∧ Even q ∧
  p = 2^(2*(k-m)) - 1 ∧ q = 2^(2*m-4) ∧
  p * q = 2^(2*m-4) * (2^(2*(k-m)) - 1) ∧
  q > p ∧ p > 2^(m-2) * (2^(k-m) - 1)


lemma quadratic_structure (a b c d k m : ℕ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h_order : a < b ∧ b < c ∧ c < d)
  (h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h_prod : a * d = b * c)
  (h_sum1 : a + d = 2^k)
  (h_sum2 : b + c = 2^m) :
  ∃ u v : ℕ, Odd u ∧ Odd v ∧
  u^2 = 2^(2*k-2) - a*d ∧
  v^2 = 2^(2*m-2) - b*c ∧
  a = 2^(k-1) - u ∧ d = 2^(k-1) + u ∧
  b = 2^(m-1) - v ∧ c = 2^(m-1) + v :=
  quadratic_roots_constraint a b c d k m h_pos h_order h_odd h_prod h_sum1 h_sum2


lemma diophantine_analysis (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 2) (h_order : k > m) :
  ∃ p q : ℕ, p * q = 2^(2*m-4) * (2^(2*(k-m)) - 1) ∧
  (Odd p ∧ Even q ∨ Even p ∧ Odd q) ∧
  p > 2^(m-2) * (2^(k-m) - 1) ∧ q > p :=
  diophantine_constraint k m hk hm h_order


lemma case_analysis (k m : ℕ) (hk : k ≥ 2) (hm : m ≥ 3) (h_order : k > m) :
  k = 2*m - 2 := by
  
  have h_exists : ∃ p q : ℕ, Odd p ∧ Even q ∧
    p = 2^(2*(k-m)) - 1 ∧ q = 2^(2*m-4) ∧
    p * q = 2^(2*m-4) * (2^(2*(k-m)) - 1) ∧
    q > p ∧ p > 2^(m-2) * (2^(k-m) - 1) :=
    case_existence k m hk hm h_order
  exact case_analysis_result k m hk hm h_order h_exists


lemma final_result (m : ℕ) (hm : m ≥ 3) :
  let k := 2*m - 2
  let u := 2^(2*(m-2)) - 1 + 2^(2*m-4)
  2^(k-1) - u = 1 :=
  final_calculation m hm


theorem imo_1984_p6 (a b c d k m : ℕ)
  (h_pos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
  (h_order : a < b ∧ b < c ∧ c < d)
  (h_odd : Odd a ∧ Odd b ∧ Odd c ∧ Odd d)
  (h_prod : a * d = b * c)
  (h_sum1 : a + d = 2^k)
  (h_sum2 : b + c = 2^m) :
  a = 1 := by

  
  have hk : k ≥ 2 := k_bound a d k ⟨h_pos.1, h_pos.2.2.2⟩ ⟨h_odd.1, h_odd.2.2.2⟩ h_sum1

  have hm : m ≥ 2 := m_bound b c m ⟨h_pos.2.1, h_pos.2.2.1⟩ ⟨h_odd.2.1, h_odd.2.2.1⟩ h_sum2

  
  have h_k_gt_m : k > m := k_gt_m a b c d k m h_order h_sum1 h_sum2

  
  have hm3 : m ≥ 3 := m_ge_3 a b c d k m h_pos h_order h_odd h_prod h_sum1 h_sum2

  
  have h_k_eq : k = 2*m - 2 := case_analysis k m hk hm3 h_k_gt_m

  
  obtain ⟨u, v, hu_odd, hv_odd, hu_sq, hv_sq, ha_eq, hd_eq, hb_eq, hc_eq⟩ :=
    quadratic_structure a b c d k m h_pos h_order h_odd h_prod h_sum1 h_sum2

  
  have hu_form : u = 2^(2*(m-2)) - 1 + 2^(2*m-4) :=
    u_form a b c d k m u v h_pos h_order h_odd h_prod h_sum1 h_sum2 h_k_eq
           hu_odd hv_odd hu_sq hv_sq ha_eq

  
  have h_final : 2^(k-1) - u = 1 := by
    rw [h_k_eq, hu_form]
    exact final_result m hm3

  
  
  
  rw [ha_eq]
  exact h_final
