import Myfmclearn.ints.axioms

variable (a b c x y z : Int)
variable (P Q : Prop)
theorem ZM_AnnR :
      ∀ (x : Int), x * 0 = 0
    := by
      intro a
      rw [← ZA_InvR a]
      have this : (a + (a * 0) = a) := by
        rw [← ZM_One_IdR a]
      sorry



theorem B1 :
      ¬ P ∨ ¬ Q → ¬ (P ∧ Q)
    := by
      intro h
      intro hn
      rcases h with l | r
      · exact l hn.1
      · exact r hn.2

theorem B2 :
      (P → Q) ∨ (Q → P)
    := by
      by_cases p : P
      · right
        intro h
        exact p
      · left
        intro h
        contradiction
    
theorem C2 :
      ∀ (a : Int), -(-a) = a
    := by
      intro a
      have : (-(-a) + (-a) = 0) := by
        rw [ZA_Com (-(-a)) (-a), ZA_InvR (-a), Z_Refl 0]
      sorry

axiom ZM_CanR : ∀ (u : Int), ¬ (u = 0) → ∀ (a b : Int), a * u = b * u → a = b

theorem C3 :
      ∀ (a b : Int), a * b = 0 → a = 0 ∨ b = 0
    := by
      intro a b
      intro h
      by_cases ma : (a = 0)
      · left
        exact ma
      · by_cases mb : (b = 0)
        · right
          exact mb
        · left
          apply (ZM_CanR b mb a 0)
          rw [ZM_Com 0 b, ZM_IdR]
          exact h

axiom ZM_NZD : ∀ (a b : Int), a * b = 0 → a = 0 ∨ b = 0

theorem CanR :
      ∀ (c : Int), ¬ (c = 0) → ∀ (a b : Int), a * c = b * c → a = b
    := by
      intro c
      intro hc
      intro a b
      intro h
      have : (c * (b + (-a))) = 0 := by
        rw [ZM_Com, ZAM_DistR b (-a) c]
        rw [← h]
        rw [← ZAM_DistR a (-a) c]
        rw [ZA_InvR]






