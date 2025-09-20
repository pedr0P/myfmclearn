import Myfmclearn.ints.axioms

section B

theorem B1 :
      ∀ (P Q : Prop), P ∧ Q → ¬ (¬ P ∨ ¬ Q)
    := by
      intro p q
      intro peq
      intro nh
      rcases nh with l|r
      · exact l peq.1
      · exact r peq.2

theorem B2 :
      ∀ (P Q R : Prop), (P ∧ Q → R) ↔ (P → (Q → R))
    := by
      intro p q r
      constructor
      · intro h
        intro hp
        intro hq
        have : p ∧ q := by
          constructor
          · exact hp
          · exact hq
        exact h this
      · intro h
        intro peq
        specialize h peq.1
        specialize h peq.2
        exact h
end B

section C

set_option pp.parens false

theorem C1 :
      ∀ (a b : Int), a
    := by
      sorry

theorem C2 :
      ∀ (a b : Int), -(a + -b) = b + -a
    := by
      intro a b
      calc -(a + -b)
        _ = -(a + -b) + l := by rw []





theorem lemma :
      ∀ (a b c : Int), a = b → a + c = b + c
    := by
      intro a b c
      intro h
      have this : a + c = b + c := congrArg (·  + c) h
      exact this


theorem lemma1 :
      ∀ (a b c : Int), a + c = b + c → a = b
    := by
      intro a b c
      intro h
      have this : a + c + -c = b + c + -c := congrArg (· + (-c)) h
      have that : a + 0 = b + 0 := by
        rw [← ZA_InvR c]
        rw [← ZA_Ass a c (-c), ← ZA_Ass b c (-c)]
        exact this
      rw [← ZA_IdR a, ← ZA_IdR b]
      exact that

end C
