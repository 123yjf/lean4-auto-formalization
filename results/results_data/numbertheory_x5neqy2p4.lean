import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic



theorem numbertheory_x5neqy2p4 : ¬ ∃ x y : ℤ, x^5 = y^2 + 4 := by
  classical
  
  rintro ⟨x, y, hxy⟩
  
  have hZMod : (x : ZMod 11)^5 = (y : ZMod 11)^2 + (4 : ZMod 11) := by
    
    simpa [map_pow, map_add, Int.castRingHom] using
      congrArg (Int.castRingHom (ZMod 11)) hxy
  
  have : ¬ ∃ a b : ZMod 11, a ^ 5 = b ^ 2 + (4 : ZMod 11) := by decide
  exact this ⟨(x : ZMod 11), (y : ZMod 11), hZMod⟩
