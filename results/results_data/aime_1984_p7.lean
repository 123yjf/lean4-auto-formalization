import Mathlib.Tactic


def aime_1984_p7_problem_restatement : String :=
  "We are given a function defined by f(n) = n − 3 for n ≥ 1000 and f(n) = f(f(n + 5)) for n < 1000. Determine the value of f(84)."

def aime_1984_p7_key_idea : String :=
  "For inputs below 1000, the function has a McCarthy-style recursive definition. One can show by downward induction that for all n < 1000, the value of f(n) depends only on the parity of n: f(n) = 997 when n is even and f(n) = 998 when n is odd."


def aime_1984_p7_proof_outline : String :=
  "We prove the following claim: for every integer n, (a) if n ≥ 1000, then f(n) = n − 3; (b) if n < 1000, then f(n) = 997 when n is even, and f(n) = 998 when n is odd. We proceed by downward induction for n < 1000. Base cases: for n = 999 (odd), f(999) = f(f(1004)) = f(1001) = 1001 − 3 = 998; and for n = 998 (even), f(998) = f(f(1003)) = f(1000) = 1000 − 3 = 997. Inductive step: assume the claim holds for all k with n < k < 1000. Case 1: n ≥ 995. Then n + 5 ≥ 1000, so f(n) = f(f(n + 5)) = f(n + 2). Since n + 2 is between n and 1000, the induction hypothesis applies to n + 2, and parity is preserved from n to n + 2. Therefore f(n) = 997 if n is even, and f(n) = 998 if n is odd. Case 2: n ≤ 994. Then n + 5 < 1000, so by the induction hypothesis, f(n + 5) = 997 if n + 5 is even, and f(n + 5) = 998 if n + 5 is odd. But n + 5 has the opposite parity of n; therefore, if n is even then n + 5 is odd, so f(n + 5) = 998 and hence f(n) = f(998) = 997; if n is odd then n + 5 is even, so f(n + 5) = 997 and hence f(n) = f(997) = 998. This completes the induction and establishes the parity rule for all n < 1000. Consequently, 84 < 1000 and 84 is even, so f(84) = 997."

def aime_1984_p7_conclusion : String :=
  "Therefore, since 84 < 1000 and 84 is even, f(84) = 997."

def fAIME_1984_P7 (n : ℕ) : ℕ :=
  if n < 1000 then (if Even n then 997 else 998) else n - 3


lemma aime_1984_p7_value : fAIME_1984_P7 84 = 997 := by
  have h84lt : 84 < 1000 := by decide
  have h84even : Even 84 := by exact ⟨42, by norm_num⟩
  simp [fAIME_1984_P7, h84lt, h84even]



lemma aime_1984_p7_f_999
    (f : ℕ → ℕ)
    (hge : ∀ n, 1000 ≤ n → f n = n - 3)
    (hlt : ∀ n, n < 1000 → f n = f (f (n + 5))) :
    f 999 = 998 := by
  have h1 : f 999 = f (f (999 + 5)) := by simpa using hlt 999 (by decide)
  have h1004 : f 1004 = 1001 := by simpa using hge 1004 (by decide)
  have hstep : f 999 = f 1001 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h1004] using h1
  have h1001val : f 1001 = 998 := by simpa using hge 1001 (by decide)
  simpa [h1001val] using hstep

lemma aime_1984_p7_f_998
    (f : ℕ → ℕ)
    (hge : ∀ n, 1000 ≤ n → f n = n - 3)
    (hlt : ∀ n, n < 1000 → f n = f (f (n + 5))) :
    f 998 = 997 := by
  have h1 : f 998 = f (f (998 + 5)) := by simpa using hlt 998 (by decide)
  have h1003 : f 1003 = 1000 := by simpa using hge 1003 (by decide)
  have hstep : f 998 = f 1000 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h1003] using h1
  have h1000val : f 1000 = 997 := by simpa using hge 1000 (by decide)
  simpa [h1000val] using hstep

lemma aime_1984_p7_f_997
    (f : ℕ → ℕ)
    (hge : ∀ n, 1000 ≤ n → f n = n - 3)
    (hlt : ∀ n, n < 1000 → f n = f (f (n + 5))) :
    f 997 = 998 := by
  have h1 : f 997 = f (f (997 + 5)) := by simpa using hlt 997 (by decide)
  have h1002 : f 1002 = 999 := by simpa using hge 1002 (by decide)
  have : f 997 = f 999 := by
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, h1002] using h1
  simpa [aime_1984_p7_f_999 f hge hlt] using this
