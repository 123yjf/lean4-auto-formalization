import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic.Ring





def unitsDigit (n : ℕ) : ℕ := n % 10


def multiplesOf3UpTo50 : Finset ℕ := (Finset.range 17).image (fun k => 3 * k)


def sumUnitsDigits : ℕ := (multiplesOf3UpTo50).sum unitsDigit


lemma multiples_range : multiplesOf3UpTo50 = {0, 3, 6, 9, 12, 15, 18, 21, 24, 27, 30, 33, 36, 39, 42, 45, 48} := by
  
  rfl


lemma direct_enumeration :
  unitsDigit 0 + unitsDigit 3 + unitsDigit 6 + unitsDigit 9 + unitsDigit 12 +
  unitsDigit 15 + unitsDigit 18 + unitsDigit 21 + unitsDigit 24 + unitsDigit 27 +
  unitsDigit 30 + unitsDigit 33 + unitsDigit 36 + unitsDigit 39 + unitsDigit 42 +
  unitsDigit 45 + unitsDigit 48 = 78 := by
  
  unfold unitsDigit
  norm_num


theorem mathd_numbertheory_447 : sumUnitsDigits = 78 := by
  
  unfold sumUnitsDigits
  rw [multiples_range]
  
  
  exact direct_enumeration










lemma complete_cycle_sum :
  0 + 3 + 6 + 9 + 2 + 5 + 8 + 1 + 4 + 7 = 45 := by
  norm_num










lemma verify_arithmetic : 45 + 33 = 78 := by
  norm_num

lemma verify_pattern : [0, 3, 6, 9, 2, 5, 8, 1, 4, 7].sum = 45 := by
  norm_num
