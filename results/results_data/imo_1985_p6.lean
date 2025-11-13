























































import Mathlib

namespace IMO1985P6


noncomputable def seq (x1 : ℝ) : ℕ → ℝ
| 0     => x1
| (n+1) =>
  let xn := seq x1 n
  xn * (xn + (1 : ℝ) / (n+1 : ℝ))

def good (x1 : ℝ) : Prop :=
  ∀ n, 0 < seq x1 n ∧ seq x1 n < seq x1 (n+1) ∧ seq x1 (n+1) < 1


lemma step_strictMono_on_nonneg (n : ℕ) :
  StrictMonoOn (fun t : ℝ => t * (t + (1 : ℝ) / (n+1 : ℝ))) (Set.Ici 0) := by
  intro a ha b hb hlt
  
  set c : ℝ := (1 : ℝ) / (n+1 : ℝ)
  have hb0 : 0 ≤ b := hb
  have ha0 : 0 ≤ a := ha
  have hba_pos : 0 < b - a := sub_pos.mpr hlt
  have hden_pos : 0 < (n+1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
  have hc_pos : 0 < c := by simpa [c] using one_div_pos.mpr hden_pos
  have hsum_pos : 0 < a + b + c := by
    have hab_nonneg : 0 ≤ a + b := add_nonneg ha0 hb0
    have hc_le_sum : c ≤ a + b + c := by
      have := add_le_add_right hab_nonneg c
      
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hc_pos hc_le_sum
  have diff_id : (b - a) * (a + b + c) = b * (b + c) - a * (a + c) := by
    ring
  have prod_pos : 0 < (b - a) * (a + b + c) := mul_pos hba_pos hsum_pos
  have diff_pos : 0 < b * (b + c) - a * (a + c) := by
    simpa [diff_id] using prod_pos
  exact (sub_pos.mp diff_pos)

end IMO1985P6


namespace IMO1985P6


def problem_statement : Prop := ∃! x1 : ℝ, good x1


lemma quad_diff_factor (a b c : ℝ) :
    b * (b + c) - a * (a + c) = (b - a) * (a + b + c) := by
  ring



lemma problem_statement_def : problem_statement ↔ ∃! x1 : ℝ, good x1 := Iff.rfl



def imo_1985_p6 : Prop := ∃! x1 : ℝ, good x1
@[simp] lemma imo_1985_p6_iff : imo_1985_p6 ↔ ∃! x1 : ℝ, good x1 := Iff.rfl


lemma strictMonoOn_mul_add {c : ℝ} (hc : 0 < c) :
    StrictMonoOn (fun t : ℝ => t * (t + c)) (Set.Ici (0:ℝ)) := by
  intro a ha b hb hlt
  have h1 : 0 < b - a := sub_pos.mpr hlt
  have h2 : 0 < a + b + c := by
    have hab : 0 ≤ a + b := add_nonneg ha hb
    have hc_le_sum : c ≤ a + b + c := by
      have := add_le_add_right hab c
      simpa [add_comm, add_left_comm, add_assoc] using this
    exact lt_of_lt_of_le hc hc_le_sum
  have diff_id : (b - a) * (a + b + c) = b * (b + c) - a * (a + c) := by
    ring
  have prod_pos : 0 < (b - a) * (a + b + c) := mul_pos h1 h2
  have hdiff_pos : 0 < b * (b + c) - a * (a + c) := by
    simpa [diff_id] using prod_pos
  exact (sub_pos.mp hdiff_pos)



lemma strictMonoOn_step (n : ℕ) :
    StrictMonoOn (fun t : ℝ => t * (t + (1 : ℝ) / (n+1 : ℝ))) (Set.Ici (0:ℝ)) := by
  have hpos : 0 < (n+1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hc : 0 < (1 : ℝ) / (n+1 : ℝ) := one_div_pos.mpr hpos
  simpa using strictMonoOn_mul_add (c := (1 : ℝ) / (n+1 : ℝ)) hc


lemma diff_step_succ (x y : ℝ) (n : ℕ) :
    x*(x + 1/(n+1 : ℝ)) - y*(y + 1/(n+1 : ℝ))
      = (x - y) * (x + y + 1/(n+1 : ℝ)) := by
  simpa [add_comm, add_left_comm, add_assoc] using quad_diff_factor y x (1 / (n+1 : ℝ))


lemma diff_step {n : ℕ} (hn : 0 < n) (x y : ℝ) :
    x * (x + 1 / (n : ℝ)) - y * (y + 1 / (n : ℝ))
      = (x - y) * (x + y + 1 / (n : ℝ)) := by
  simpa [add_comm, add_left_comm, add_assoc] using quad_diff_factor y x (1 / (n : ℝ))


lemma diff_seq_succ (x1 y1 : ℝ) (n : ℕ) :
    seq x1 (n+1) - seq y1 (n+1)
      = (seq x1 n - seq y1 n) * (seq x1 n + seq y1 n + 1/(n+1 : ℝ)) := by
  
  dsimp [seq]
  set x := seq x1 n
  set y := seq y1 n
  simpa [x, y] using diff_step_succ x y n


lemma good_lower_bound {x1 : ℝ} (hg : good x1) (n : ℕ) :
    1 - 1 / (n+1 : ℝ) < seq x1 n := by
  rcases hg n with ⟨hn_pos, hn_lt, _⟩
  
  have hstep : seq x1 n * (1 : ℝ)
      < seq x1 n * (seq x1 n + 1 / (n+1 : ℝ)) := by
    
    simpa [seq, one_mul] using hn_lt
  
  have hsum : 1 < seq x1 n + 1 / (n+1 : ℝ) := by
    
    exact (mul_lt_mul_left hn_pos).mp hstep
  
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using (sub_lt_sub_right hsum (1 / (n+1 : ℝ)))


lemma diff_growth_lower_bound_of_pos
    {x1 y1 : ℝ} (hx : good x1) (hy : good y1) (n : ℕ)
    (hpos : 0 < seq x1 n - seq y1 n) :
    (seq x1 n - seq y1 n) * (2 - 1 / (n+1 : ℝ))
      < seq x1 (n+1) - seq y1 (n+1) := by
  
  have hx_lb : 1 - 1 / (n+1 : ℝ) < seq x1 n := good_lower_bound hx n
  have hy_lb : 1 - 1 / (n+1 : ℝ) < seq y1 n := good_lower_bound hy n
  
  have hmult_strict : (2 - 1 / (n+1 : ℝ))
      < (seq x1 n + seq y1 n + 1 / (n+1 : ℝ)) := by
    have : (1 - 1 / (n+1 : ℝ)) + (1 - 1 / (n+1 : ℝ))
        < seq x1 n + seq y1 n := by
      exact add_lt_add hx_lb hy_lb
    
    set a : ℝ := 1 / (n+1 : ℝ)
    have h' : (1 - a) + (1 - a) + a < seq x1 n + seq y1 n + a := by
      simpa [a] using add_lt_add_right this a
    have hsum_eq : (1 - a) + (1 - a) + a = 2 - a := by
      ring
    have : (2 - a) < seq x1 n + seq y1 n + a := by
      simpa [hsum_eq] using h'
    simpa [a] using this
  
  have : (seq x1 n - seq y1 n) * (2 - 1 / (n+1 : ℝ))
      < (seq x1 n - seq y1 n) * (seq x1 n + seq y1 n + 1 / (n+1 : ℝ)) :=
    mul_lt_mul_of_pos_left hmult_strict hpos
  simpa [diff_seq_succ] using this



lemma mult_lower_ge_three_halves (n : ℕ) (hn : 1 ≤ n) :
    (3 / 2 : ℝ) ≤ 2 - 1 / (n+1 : ℝ) := by
  
  have hle_nat : (2 : ℕ) ≤ n.succ := Nat.succ_le_succ hn
  have hle : (2 : ℝ) ≤ (n+1 : ℝ) := by exact_mod_cast hle_nat
  have hpos2 : 0 < (2 : ℝ) := by norm_num
  have hdiv : (1 : ℝ) / (n+1 : ℝ) ≤ (1 : ℝ) / 2 := by
    
    simpa using (one_div_le_one_div_of_le hpos2 hle)
  
  have : (3 / 2 : ℝ) ≤ 2 - 1 / (n+1 : ℝ) := by linarith [hdiv]
  simpa using this


lemma diff_growth_ge_three_halves
    {x1 y1 : ℝ} (hx : good x1) (hy : good y1)
    (n : ℕ) (hn : 1 ≤ n)
    (hpos : 0 < seq x1 n - seq y1 n) :
    (seq x1 n - seq y1 n) * (3 / 2 : ℝ)
      < seq x1 (n+1) - seq y1 (n+1) := by
  
  have hchain :
      (seq x1 n - seq y1 n) * (3 / 2 : ℝ)
        ≤ (seq x1 n - seq y1 n) * (2 - 1 / (n+1 : ℝ)) := by
    have hnonneg : 0 ≤ seq x1 n - seq y1 n := le_of_lt hpos
    exact mul_le_mul_of_nonneg_left (mult_lower_ge_three_halves n hn) hnonneg
  have hstrict := diff_growth_lower_bound_of_pos hx hy n hpos
  exact lt_of_le_of_lt hchain hstrict



lemma seq_nonneg_of_nonneg {x1 : ℝ} (hx : 0 ≤ x1) : ∀ n, 0 ≤ seq x1 n
| 0 => hx
| (n+1) => by
  have hxn : 0 ≤ seq x1 n := seq_nonneg_of_nonneg hx n
  have hdenpos : 0 < (n+1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  have hc : 0 ≤ 1 / (n+1 : ℝ) := one_div_nonneg.mpr (le_of_lt hdenpos)
  have hmul : 0 ≤ seq x1 n * (seq x1 n + 1 / (n+1 : ℝ)) := by
    exact mul_nonneg hxn (add_nonneg hxn hc)
  dsimp [seq]
  simpa using hmul





lemma strictMonoOn_in_x1_seq (n : ℕ) :
  StrictMonoOn (fun t : ℝ => seq t n) (Set.Ici 0) := by
  induction' n with n ih
  · intro a ha b hb hlt; simpa [seq] using hlt
  · intro a ha b hb hlt
    have hprev : seq a n < seq b n := ih ha hb hlt
    have ha0 : 0 ≤ seq a n := seq_nonneg_of_nonneg (by exact ha) n
    have hb0 : 0 ≤ seq b n := seq_nonneg_of_nonneg (by exact hb) n
    have hc_pos : 0 < (1 : ℝ) / (n+1 : ℝ) := by
      have : 0 < (n+1 : ℝ) := by exact_mod_cast Nat.succ_pos n
      exact one_div_pos.mpr this
    have hmult_pos : 0 < seq b n + seq a n + 1 / (n+1 : ℝ) := by
      have hsum_nonneg : 0 ≤ seq b n + seq a n := add_nonneg hb0 ha0
      exact add_pos_of_nonneg_of_pos hsum_nonneg (by
        have : 0 < (n+1 : ℝ) := by exact_mod_cast Nat.succ_pos n
        simpa using one_div_pos.mpr this)
    have hprod_pos :
        0 < (seq b n - seq a n) * (seq b n + seq a n + 1 / (n+1 : ℝ)) :=
      mul_pos (sub_pos.mpr hprev) hmult_pos
    have hdiff_eq :
        seq b (n+1) - seq a (n+1)
          = (seq b n - seq a n) * (seq b n + seq a n + 1 / (n+1 : ℝ)) := by
      simpa [seq, add_comm] using diff_step_succ (seq b n) (seq a n) n
    have : 0 < seq b (n+1) - seq a (n+1) := by
      simpa [hdiff_eq] using hprod_pos
    exact sub_pos.mp this







lemma strictMonoOn_step (n : ) :
    StrictMonoOn (fun t :  => t * (t + 1 / (n+1 : ))) (Set.Ici (0:)) := by


lemma diff_pos_at_one_of_good {x1 y1 : ℝ}
    (hx : good x1) (hy : good y1) (hxy : y1 < x1) :
    0 < seq x1 1 - seq y1 1 := by
  have hxpos : 0 < x1 := (hx 0).1
  have hypos : 0 < y1 := (hy 0).1
  have hmono := strictMonoOn_in_x1_seq 1
  have hlt : seq y1 1 < seq x1 1 := hmono hypos.le hxpos.le hxy
  exact sub_pos.mpr hlt

  have hpos : 0 < (n+1 : ) := by exact_mod_cast Nat.succ_pos n
  have hc : 0 < (1 : ) / (n+1 : ) := one_div_pos.mpr hpos
  simpa using strictMonoOn_mul_add (c := (1 : ) / (n+1 : )) hc


lemma diff_step_succ (x y : ) (n : ) :
    x*(x + 1/(n+1 : )) - y*(y + 1/(n+1 : ))
      = (x - y) * (x + y + 1/(n+1 : )) := by


lemma one_div_nat_succ_pos (n : ℕ) : 0 < (1 : ℝ) / (n+1 : ℝ) := by
  have : 0 < (n+1 : ℝ) := by exact_mod_cast Nat.succ_pos n
  exact one_div_pos.mpr this


lemma diff_seq_succ (x1 y1 : ℝ) (n : ℕ) :
    seq x1 (n+1) - seq y1 (n+1)
      = (seq x1 n - seq y1 n) * (seq x1 n + seq y1 n + 1/(n+1 : ℝ)) := by
  
  dsimp [seq]
  set x := seq x1 n
  set y := seq y1 n
  simpa [x, y] using diff_step_succ x y n

  simpa using quad_diff_factor y x (1 / (n+1 : ))


def imo_1985_p6 : Prop := ! x1 : , good x1
@[simp] lemma imo_1985_p6_iff : imo_1985_p6  ! x1 : , good x1 := Iff.rfl

    x * (x + 1 / (n : ℝ)) - y * (y + 1 / (n : ℝ))
      = (x - y) * (x + y + 1 / (n : ℝ)) := by
  simpa [add_comm, add_left_comm, add_assoc] using quad_diff_factor y x (1 / (n : ℝ))

-/


lemma diff_pos_at_one_of_good {x1 y1 : ℝ}
    (hx : good x1) (hy : good y1) (hxy : y1 < x1) :
    0 < seq x1 1 - seq y1 1 := by
  have hxpos : 0 < x1 := (hx 0).1
  have hypos : 0 < y1 := (hy 0).1
  have hmono := strictMonoOn_in_x1_seq 1
  have hlt : seq y1 1 < seq x1 1 := hmono hypos.le hxpos.le hxy
  exact sub_pos.mpr hlt



lemma diff_ge_pow_three_halves_succ
    {x1 y1 : ℝ} (hx : good x1) (hy : good y1) (hxy : y1 < x1) :
    ∀ m : ℕ, (seq x1 (m+1) - seq y1 (m+1)) ≥ (3/2 : ℝ)^m * (seq x1 1 - seq y1 1) := by
  intro m
  induction' m with m ih
  · 
    simp [pow_zero, one_mul]
  · 
    have base_pos : 0 < seq x1 1 - seq y1 1 :=
      diff_pos_at_one_of_good hx hy hxy
    have hpos_lower : 0 < (3/2 : ℝ)^m * (seq x1 1 - seq y1 1) :=
      mul_pos (pow_pos (by norm_num : 0 < (3/2 : ℝ)) _) base_pos
    have hpos : 0 < seq x1 (m+1) - seq y1 (m+1) :=
      lt_of_lt_of_le hpos_lower ih
    have hn : 1 ≤ m+1 := by
      exact Nat.succ_le_succ (Nat.zero_le m)
    have hstep := diff_growth_ge_three_halves hx hy (m+1) hn hpos
    have hge : (3/2 : ℝ) * (seq x1 (m+1) - seq y1 (m+1)) ≤
        seq x1 (m+2) - seq y1 (m+2) := by
      simpa [mul_comm] using (le_of_lt hstep)
    calc
      (seq x1 (m+2) - seq y1 (m+2))
          ≥ (3/2 : ℝ) * (seq x1 (m+1) - seq y1 (m+1)) := hge
      _ ≥ (3/2 : ℝ) * ((3/2 : ℝ)^m * (seq x1 1 - seq y1 1)) := by
        exact mul_le_mul_of_nonneg_left ih (by norm_num : 0 ≤ (3/2 : ℝ))
      _ = (3/2 : ℝ)^(m+1) * (seq x1 1 - seq y1 1) := by
        simp [pow_succ, mul_left_comm, mul_assoc]


end IMO1985P6
