import Mathlib

open Finset

namespace AMC12A_2020_P4


@[simp] def thousands : Finset ℕ := {2, 4, 6, 8}
@[simp] def mid : Finset ℕ := {0, 2, 4, 6, 8}
@[simp] def units : Finset ℕ := {0}
@[simp] def hundreds : Finset ℕ := mid
@[simp] def tens : Finset ℕ := mid
@[simp] def div5 : Finset ℕ := {0, 5}

@[simp] lemma units_is_even_inter_div5 : (mid ∩ div5) = units := by
  classical
  simp [mid, div5, units]


lemma card_thousands : thousands.card = 4 := by simp [thousands]
lemma card_mid       : mid.card = 5       := by simp [mid]
lemma card_units     : units.card = 1     := by simp [units]


lemma count_tuples :
    (((thousands.product mid).product (mid.product units))).card = 100 := by
  classical
  have hprod :
      (((thousands.product mid).product (mid.product units))).card
        = thousands.card * mid.card * mid.card * units.card := by
    simp [Finset.card_product, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
  simpa [card_thousands, card_mid, card_units, Nat.mul_assoc] using hprod


 theorem amc12a_2020_p4 :
    thousands.card * hundreds.card * tens.card * units.card = 100 := by
  classical
  have ht : thousands.card = 4 := card_thousands
  have hh : hundreds.card = 5 := by simpa [hundreds, mid] using card_mid
  have tt : tens.card = 5 := by simpa [tens, mid] using card_mid
  have hu : units.card = 1 := card_units
  simpa [ht, hh, tt, hu]

end AMC12A_2020_P4
