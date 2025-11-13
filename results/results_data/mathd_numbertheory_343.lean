import Std.Tactic.Decide
import Mathlib.Tactic


 theorem mathd_numbertheory_343 :
   (1 * 3 * 5 * 7 * 9 * 11) % 10 = 5 := by
  
  decide



def unitsDigit (n : ℕ) : ℕ := n % 10


 theorem mathd_numbertheory_343_unitsDigit :
   unitsDigit (1 * 3 * 5 * 7 * 9 * 11) = 5 := by
  decide
