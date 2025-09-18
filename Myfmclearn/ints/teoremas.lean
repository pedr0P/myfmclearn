import Myfmclearn.ints.axioms

variable (a b c x y z : Int)

theorem ZA_idL :
      ∀ (a : Int), 0 + a = a
    := by
      intro a
      rw [ZA_Com 0 a, ZA_IdR a]

theorem ZM_idL :
      ∀ (a : Int), 0 * a = 0
    := by
      intro a
      rw [ZM_Com 0 a, ZM_IdR a]

theorem Z_Inv :
      ∀ (a : Int), -(-a) = a
    := by
      intro a
      have : ∀ (a : Int ), -a + -(-a) = 0 := by
        intro x
        rw [ZA_InvR (-x), Z_Refl 0]
      specialize this a
      sorry

theorem ZA_idU :
      ∀ (u v : Int), (u + v = u) ∧ (v + 0 = v) → u = v
      := by

theorem ZA_CanR :
      ∀ (c x y : Int), x + c = y + c → x = y
    := by
      intro c x y
      intro h
      sorry



theorem noname  :
      ∀ (a b : Int), ab = 0 → a = 0 ∨ b = 0 → ∀ (a b c : Int), ¬(c = 0) → (ac = bc → a = b)
    := by
      sorry
