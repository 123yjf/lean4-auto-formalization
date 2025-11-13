import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.List.Lemmas
set_option maxRecDepth 200000
set_option maxHeartbeats 500000



def goodK (k : ℕ) : Prop :=
  k^2 ≤ 70*k - 1000 ∧ 70*k - 1000 < (k+1)^2


def condN (n : ℕ) : Prop :=
  0 < n ∧ (n + 1000) % 70 = 0 ∧ (n + 1000) / 70 = Nat.sqrt n


def goodKB (k : ℕ) : Bool :=
  (decide (1000 ≤ 70*k)) &&
  (decide (k^2 ≤ 70*k - 1000)) &&
  (decide (70*k - 1000 < (k+1)^2))


def condNB (n : ℕ) : Bool :=
  (decide (0 < n)) && (((n + 1000) % 70) == 0) && (((n + 1000) / 70) == Nat.sqrt n)

def ks : List Nat := (List.range 101).filter goodKB

def ns : List Nat := ks.map (fun k => 70*k - 1000)

lemma ks_eq : ks = [20, 21, 47, 48, 49, 50] := by
  decide

lemma ns_eq : ns = [400, 470, 2290, 2360, 2430, 2500] := by
  simpa [ns, ks_eq]

@[simp] theorem amc12b_2020_p21 : ns.length = 6 := by
  simpa [ns_eq]
