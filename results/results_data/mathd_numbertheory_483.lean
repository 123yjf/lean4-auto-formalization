import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Fib
import Mathlib.Tactic


private lemma fib_pair_period6_mod4 (n : ℕ) :
    ((Nat.fib (n+6) : ZMod 4), (Nat.fib (n+7) : ZMod 4))
    = ((Nat.fib n : ZMod 4), (Nat.fib (n+1) : ZMod 4)) := by
  induction' n with n ih
  · 
    decide
  · 
    
    have ih₁ : (Nat.fib (n+6) : ZMod 4) = Nat.fib n := by
      simpa using congrArg Prod.fst ih
    have ih₂ : (Nat.fib (n+7) : ZMod 4) = Nat.fib (n+1) := by
      simpa using congrArg Prod.snd ih
    
    have h8 : (Nat.fib (n+8) : ZMod 4) = Nat.fib (n+2) := by
      calc
        (Nat.fib (n+8) : ZMod 4)
            = ((Nat.fib (n+7) + Nat.fib (n+6)) : ZMod 4) := by
                simpa [Nat.fib_succ_succ, Nat.cast_add]
        _ = (Nat.fib (n+1) + Nat.fib n : ZMod 4) := by simpa [ih₁, ih₂]
        _ = (Nat.fib (n+2) : ZMod 4) := by simpa [Nat.fib_succ_succ, Nat.cast_add]
    
    exact Prod.ext ih₂ h8


private lemma fib_period6_mod4 (n : ℕ) :
    (Nat.fib (n+6) : ZMod 4) = Nat.fib n := by
  simpa using congrArg Prod.fst (fib_pair_period6_mod4 n)

private lemma fib_period6k_mod4 (n k : ℕ) :
    (Nat.fib (n + 6*k) : ZMod 4) = Nat.fib n := by
  induction' k with k ih
  · simp
  · have hstep : (Nat.fib (n + 6 * (k+1)) : ZMod 4) = Nat.fib (n + 6 * k) := by
      simpa [Nat.mul_succ, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
        using fib_period6_mod4 (n := n + 6 * k)
    simpa using hstep.trans ih


 theorem mathd_numbertheory_483 :
   ((Nat.fib 100 : ZMod 4) = 3) := by
  
  have : (Nat.fib 100 : ZMod 4) = Nat.fib 4 := by
    simpa using fib_period6k_mod4 (n := 4) (k := 16)
  
  simpa [this]
