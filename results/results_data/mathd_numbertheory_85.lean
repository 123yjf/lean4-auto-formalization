import Mathlib.Tactic
import Mathlib.Data.Nat.Digits.Defs



def problem_restatement_mathd_numbertheory_85 : String :=
  "Convert the base-three number 1222₃ to its base-ten value."



 theorem mathd_numbertheory_85_convert_1222₃_to_base10 :
    Nat.ofDigits 3 [2, 2, 2, 1] = 53 := by
  decide



def horner (b : Nat) (ds : List Nat) : Nat :=
  ds.foldl (fun acc d => acc * b + d) 0


 theorem mathd_numbertheory_85_horner :
    horner 3 [1, 2, 2, 2] = 53 := by
  simp [horner]

