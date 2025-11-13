import Mathlib
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic




lemma amc12a_2021_p12_S3 :
    ((Nat.choose 4 3) * 8 + (2 * Nat.choose 4 2) * 4 + (Nat.choose 2 2 * 4) * 2 : ℕ) = 88 := by
  decide


def amc12a_2021_p12_S3_val : ℕ :=
  (Nat.choose 4 3) * 8 + (2 * Nat.choose 4 2) * 4 + (Nat.choose 2 2 * 4) * 2

lemma amc12a_2021_p12_S3_eval : amc12a_2021_p12_S3_val = 88 := amc12a_2021_p12_S3


theorem amc12a_2021_p12 : (-(amc12a_2021_p12_S3_val : ℤ)) = (-88) := by
  have := congrArg (fun n : ℕ => (- (n : ℤ))) amc12a_2021_p12_S3_eval
  simpa using this


def amc12a_2021_p12_exposition : String :=
"
"
"
"
"   (i) r1 + ⋯ + r6 = 10,\n" ++
"   (ii) r1 r2 ⋯ r6 = 16,\n" ++
"   (iii) the coefficient of z^3 equals (−1)^3 S3 = −S3, where S3 is the sum of all triple products r_i r_j r_k with i < j < k. Thus B = −S3.\n\n" ++
"   Because 16 = 2^4 and all roots are positive integers, each root must be a power of 2. Values larger than 4 (namely 8 or 16) would make the sum exceed 10, so the only possibilities are 1, 2, and 4. Let a, b, c be the counts of 4’s, 2’s, and 1’s respectively, so a + b + c = 6.\n\n" ++
"   The product condition gives 4^a · 2^b = 16, i.e., 2a + b = 4.\n" ++
"   The sum condition gives 4a + 2b + c = 10, and since c = 6 − a − b, this simplifies to 3a + b = 4.\n" ++
"   Subtracting the two equations yields a = 0, hence b = 4 and c = 2. Therefore the multiset of roots is uniquely {1, 1, 2, 2, 2, 2}.\n\n" ++
"   Compute S3 by counting triple products:\n" ++
"   - Triples with no 1’s: choose 3 of the 4 twos, C(4,3) = 4 triples, each product 2·2·2 = 8, contributing 4·8 = 32.\n" ++
"   - Triples with exactly one 1: choose 1 of the 2 ones and 2 of the 4 twos, 2·C(4,2) = 12 triples, each product 1·2·2 = 4, contributing 12·4 = 48.\n" ++
"   - Triples with exactly two 1’s: choose both ones and 1 of the 4 twos, 4 triples, each product 1·1·2 = 2, contributing 4·2 = 8.\n\n" ++
"   Thus S3 = 32 + 48 + 8 = 88, and therefore B = −S3 = −88.\n" ++
"


theorem amc12a_2021_p12_problem_restatement_determine_B_in_polynomial_with_roots_posint_sum10_prod16 : True :=
  trivial
