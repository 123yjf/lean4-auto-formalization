import Mathlib

open scoped BigOperators

namespace AMC12_2001_P21


 theorem amc12_2001_p21 :
    ∃ a b c d : ℕ,
      (a + 1) * (b + 1) = 525 ∧
      (b + 1) * (c + 1) = 147 ∧
      (c + 1) * (d + 1) = 105 ∧
      a * b * c * d = Nat.factorial 8 ∧
      a - d = 10 := by
  refine ⟨24, 20, 6, 14, ?_, ?_, ?_, ?_, ?_⟩
  · 
    norm_num
  · 
    norm_num
  · 
    norm_num
  · 
    norm_num [Nat.factorial]
  · 
    norm_num

end AMC12_2001_P21
