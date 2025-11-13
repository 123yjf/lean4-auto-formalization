













import Mathlib
open ZMod

namespace AMC12A_2021_P8


@[simp] def d0 : ZMod 2 := 0
@[simp] def d1 : ZMod 2 := 0
@[simp] def d2 : ZMod 2 := 1
@[simp] def d3 : ZMod 2 := 1
@[simp] def d4 : ZMod 2 := 1
@[simp] def d5 : ZMod 2 := 0
@[simp] def d6 : ZMod 2 := 1
@[simp] def d7 : ZMod 2 := 0
@[simp] def d8 : ZMod 2 := 0
@[simp] def d9 : ZMod 2 := 1
@[simp] def d10 : ZMod 2 := 1
@[simp] def d11 : ZMod 2 := 1
@[simp] def d12 : ZMod 2 := 0
@[simp] def d13 : ZMod 2 := 1


lemma parity_block_eval :
    [d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13]
  = ([0, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 1, 0, 1] : List (ZMod 2)) := by
  simp



open Nat
@[simp] def pat : Fin 7 → ZMod 2 := ![0, 0, 1, 1, 1, 0, 1]
@[simp] def parity (n : Nat) : ZMod 2 := pat ⟨n % 7, Nat.mod_lt _ (by decide : 0 < 7)⟩

@[simp] lemma mod2021 : 2021 % 7 = 5 := by decide
@[simp] lemma mod2022 : 2022 % 7 = 6 := by decide
@[simp] lemma mod2023 : 2023 % 7 = 0 := by decide

@[simp] lemma parity2021_mod : parity 2021 = 0 := by
  simp [parity, pat, mod2021]
@[simp] lemma parity2022_mod : parity 2022 = 1 := by
  simp [parity, pat, mod2022]
@[simp] lemma parity2023_mod : parity 2023 = 0 := by
  simp [parity, pat, mod2023]




@[simp] def dR : ℕ → ZMod 2
| 0 => 0
| 1 => 0
| 2 => 1
| n+3 => dR (n+2) + dR n


@[simp] def state (n : ℕ) : ZMod 2 × ZMod 2 × ZMod 2 := (dR n, dR (n+1), dR (n+2))


@[simp] def step : (ZMod 2 × ZMod 2 × ZMod 2) → (ZMod 2 × ZMod 2 × ZMod 2)
| (a,b,c) => (b, c, c + a)


lemma state_succ (n : ℕ) : state (n+1) = step (state n) := by
  simp [state, step, dR]


@[simp] lemma add_one_one_z2 : (1 : ZMod 2) + 1 = 0 := by decide


lemma state7_eq_state0 : state 7 = state 0 := by
  
  simp [state, dR]


lemma state_periodic_7 (n : ℕ) : state (n+7) = state n := by
  induction' n with n ih
  · simpa [Nat.zero_add] using state7_eq_state0
  · 
    have h := congrArg step ih
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, state_succ] using h


lemma dR_periodic7 (n : ℕ) : dR (n+7) = dR n := by
  simpa [state] using congrArg Prod.fst (state_periodic_7 n)


lemma dR_add_7_mul (r q : ℕ) : dR (r + 7*q) = dR r := by
  induction' q with q ih
  · simp
  · simpa [Nat.mul_succ, Nat.add_assoc] using (dR_periodic7 (n := r + 7*q)).trans ih

lemma dR_mod (n : ℕ) : dR n = dR (n % 7) := by
  have h := dR_add_7_mul (r := n % 7) (q := n / 7)
  
  simpa [Nat.mod_add_div, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h


@[simp] lemma dR_3 : dR 3 = 1 := by decide
@[simp] lemma dR_4 : dR 4 = 1 := by decide
@[simp] lemma dR_5 : dR 5 = 0 := by decide
@[simp] lemma dR_6 : dR 6 = 1 := by decide
@[simp] lemma dR_7 : dR 7 = 0 := by decide
@[simp] lemma dR_8 : dR 8 = 0 := by decide
@[simp] lemma dR_9 : dR 9 = 1 := by decide




@[simp] def parity2021 : ZMod 2 := d5  
@[simp] def parity2022 : ZMod 2 := d6  
@[simp] def parity2023 : ZMod 2 := d0  


 theorem amc12a_2021_p8_parities :
    parity2021 = 0 ∧ parity2022 = 1 ∧ parity2023 = 0 := by
  simp

end AMC12A_2021_P8
