import Myfmclearn.Ints.axioms

variable (a b c x y z : Int)

theorem ZA_idL :
    ∀ (x : Int), 0 + x = x
    := by
  intro x
  rw [ZA_Com 0 x, ZA_IdR x]

theorem Z_Inv :
    ∀ (x : Int), -(-x) = x
    := by
  intro x
  have : -x + -(-x) = 0 := by
    rw [ZA_InvR (-x), Z_Refl 0]
  sorry

