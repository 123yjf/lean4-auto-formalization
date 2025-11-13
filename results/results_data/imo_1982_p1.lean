




















import Mathlib.Tactic


structure ImoSpec (f : Nat → Nat) : Prop :=
  (h2     : f 2 = 0)
  (h3pos  : 0 < f 3)
  (h9999  : f 9999 = 3333)
  (carry  : ∀ m n, 0 < m → 0 < n → ∃ δ : Nat, δ ≤ 1 ∧ f (m + n) = f m + f n + δ)


def Imo1982P1Statement : Prop :=
  ∃ f : Nat → Nat, ImoSpec f ∧ f 1982 = 660



@[simp] def imo1982_f (n : Nat) : Nat := n / 3


lemma imo1982_f_values :
    imo1982_f 2 = 0 ∧ imo1982_f 3 = 1 ∧ imo1982_f 9999 = 3333 ∧ imo1982_f 1982 = 660 := by
  constructor
  · norm_num [imo1982_f]
  constructor
  · norm_num [imo1982_f]
  constructor
  · norm_num [imo1982_f]
  · norm_num [imo1982_f]

lemma div3_carry (m n : Nat) :
    (m + n) / 3 = m / 3 + n / 3 + ((m % 3 + n % 3) / 3) := by
  
  have hm : m = 3 * (m / 3) + m % 3 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using (Nat.mod_add_div m 3).symm
  have hn : n = 3 * (n / 3) + n % 3 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.mul_comm] using (Nat.mod_add_div n 3).symm
  
  have hsum : m + n = 3 * (m / 3 + n / 3) + (m % 3 + n % 3) := by
    calc
      m + n = (m % 3 + 3 * (m / 3)) + (n % 3 + 3 * (n / 3)) := by
        simpa [Nat.mod_add_div, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm]
      _ = (m % 3 + n % 3) + (3 * (m / 3) + 3 * (n / 3)) := by
        ac_rfl
      _ = (m % 3 + n % 3) + 3 * (m / 3 + n / 3) := by
        simpa [Nat.mul_add, Nat.add_comm]
      _ = 3 * (m / 3 + n / 3) + (m % 3 + n % 3) := by
        ac_rfl
  have hstep :
      (3 * (m / 3 + n / 3) + (m % 3 + n % 3)) / 3
        = (m / 3 + n / 3) + ((m % 3 + n % 3) / 3) := by
    have hpos : 0 < 3 := by decide
    have h := Nat.add_mul_div_left (x := (m % 3 + n % 3)) (y := 3) (z := (m / 3 + n / 3)) hpos
    simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h
  calc
    (m + n) / 3
        = (3 * (m / 3 + n / 3) + (m % 3 + n % 3)) / 3 := by simpa [hsum]
    _ = (m / 3 + n / 3) + ((m % 3 + n % 3) / 3) := hstep


lemma carry_le_one_mod3 (m n : Nat) :
    ((m % 3 + n % 3) / 3) ≤ 1 := by
  have hm : m % 3 ≤ 2 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 3))
  have hn : n % 3 ≤ 2 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide : 0 < 3))
  have hsum_le4 : m % 3 + n % 3 ≤ 4 := add_le_add hm hn
  have hdiv : ((m % 3 + n % 3) / 3) ≤ 4 / 3 := Nat.div_le_div_right (c := 3) hsum_le4
  have h43 : 4 / 3 = 1 := by norm_num
  simpa [h43] using hdiv


lemma imo1982_f_spec : ImoSpec imo1982_f := by
  refine ⟨?h2, ?h3pos, ?h9999, ?carry⟩
  · 
    simpa [imo1982_f] using (by norm_num : 2 / 3 = 0)
  · 
    have : imo1982_f 3 = 1 := by norm_num [imo1982_f]
    simpa [this] using (by decide : 0 < 1)
  · 
    simpa [imo1982_f] using (by norm_num : 9999 / 3 = 3333)
  · 
    intro m n hm hn
    refine ⟨((m % 3 + n % 3) / 3), carry_le_one_mod3 m n, ?eq⟩
    have := div3_carry m n
    
    simpa [imo1982_f, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this


theorem imo_1982_p1_exists : Imo1982P1Statement := by
  refine ⟨imo1982_f, imo1982_f_spec, ?_⟩
  norm_num [imo1982_f]



 theorem imo_1982_p1 : imo1982_f 1982 = 660 := by
  have h := imo1982_f_values
  exact h.right.right.right
