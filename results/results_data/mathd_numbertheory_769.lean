import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic


 theorem mathd_numbertheory_769 :
   ((129^34 + 96^38 : ℕ) : ZMod 11) = 9 := by
   
   have h129 : ((129 : ℕ) : ZMod 11) = 8 := by decide
   have h96  : ((96  : ℕ) : ZMod 11) = 8 := by decide
   
   have h834 : ((8 : ZMod 11) ^ 34) = 4 := by decide
   have h838 : ((8 : ZMod 11) ^ 38) = 5 := by decide
   
   calc
     ((129^34 + 96^38 : ℕ) : ZMod 11)
         = ((129 : ZMod 11) ^ 34 + (96 : ZMod 11) ^ 38) := by
           simp [Nat.cast_pow, Nat.cast_add]
     _ = (8 : ZMod 11) ^ 34 + (8 : ZMod 11) ^ 38 := by simpa [h129, h96]
     _ = 4 + 5 := by simpa [h834, h838]
     _ = (9 : ZMod 11) := by decide
