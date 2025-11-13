import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 800000
set_option maxRecDepth 10000





open Nat

namespace IMO1974P3


noncomputable def s (n : ℕ) : ℕ :=
  (Finset.range (n+1)).sum (fun k => Nat.choose (2*n+1) (2*k+1) * 2^(3*k))


noncomputable def sZ (n : ℕ) : ZMod 5 :=
  (Finset.range (n+1)).sum (fun k =>
    (Nat.choose (2*n+1) (2*k+1) : ZMod 5) * ((8 : ZMod 5) ^ k))


@[simp] def stmt : Prop := ∀ n : ℕ, ¬ (5 ∣ s n)

lemma four_ne_zero_mod5 : (4 : ZMod 5) ≠ 0 := by decide

lemma four_is_unit_mod5 : IsUnit (4 : ZMod 5) := by
  refine ⟨⟨4, 4, ?h1, ?h2⟩, rfl⟩
  · decide
  · decide


def target (n : ℕ) : Prop := (s n) % 5 ≠ 0


noncomputable def d : ℕ → ZMod 5
  | 0 => 0
  | 1 => 4
  | n+2 => 2 * (d (n+1) + d n)

@[simp] lemma d_zero : d 0 = (0 : ZMod 5) := rfl
@[simp] lemma d_one  : d 1 = (4 : ZMod 5) := rfl
lemma d_succ_succ (n : ℕ) : d (n+2) = 2 * (d (n+1) + d n) := rfl


private lemma d_24_eq : d 24 = d 0 := by decide
private lemma d_25_eq : d 25 = d 1 := by decide


lemma d_period24_pair : ∀ n, d (n+24) = d n ∧ d (n+25) = d (n+1)
  | 0 => by
    exact ⟨by simpa using d_24_eq, by simpa using d_25_eq⟩
  | n+1 => by
    rcases d_period24_pair n with ⟨hA, hB⟩
    
    have hC : d (n+26) = d (n+2) := by
      calc
        d (n+26) = 2 * (d (n+25) + d (n+24)) := by simpa using d_succ_succ (n+24)
        _ = 2 * (d (n+1) + d n) := by simpa [hA, hB]
        _ = d (n+2) := by simpa using d_succ_succ n
    
    exact ⟨by simpa [Nat.add_assoc] using hB, by simpa [Nat.add_assoc] using hC⟩


lemma d_period24 (n : ℕ) : d (n+24) = d n :=
  (d_period24_pair n).1


lemma d_add_period (n t : ℕ) : d (n + 24*t) = d n := by
  induction' t with t ht
  · simp
  · have hstep0 : d (n + 24*t + 24) = d (n + 24*t) := d_period24 (n + 24*t)
    have hstep : d (n + (24 + 24*t)) = d (n + 24*t) := by
      simpa [Nat.add_left_comm, Nat.add_comm, Nat.add_assoc] using hstep0
    calc
      d (n + 24*(t+1)) = d (n + (24 + 24*t)) := by
        simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      _ = d (n + 24*t) := hstep
      _ = d n := ht


end IMO1974P3
