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
      have : a = -(-a) := by
        calc
          a = a + 0 := by rw [ZA_IdR a]
          _ = a + (-a + -(-a)) := by rw [ZA_InvR (-a)]
          _ = (a + -a) + -(-a) := by rw [← ZA_Ass a (-a) (-(-a))]
          _ = 0 + -(-a) := by rw [ZA_InvR a]
          _ = -(-a) := by rw [ZA_idL (-(-a))]
      rw [Z_Symm a (-(-a))]
      exact this

theorem ZA_idU :
      ∀ (u v : Int), (u + v = u) ∧ (v + u = v) → u = v
      := by
        intro u v
        intro h
        obtain ⟨l, r⟩ := h
        apply l.subst
        rw [ZA_Com u v]
        exact r


theorem ZA_CanR :
      ∀ (c x y : Int), x + c = y + c → x = y
    := by
      intro c x y
      intro h
      rw [← ZA_IdR x, ← ZA_IdR y]
      rw [← ZA_InvR c]
      rw [← ZA_Ass x c (-c), ← ZA_Ass y c (-c)]
      congr



theorem noname  :
      ∀ (a b : Int), ab = 0 → a = 0 ∨ b = 0 → ∀ (a b c : Int), ¬(c = 0) → (ac = bc → a = b)
    := by
      sorry
