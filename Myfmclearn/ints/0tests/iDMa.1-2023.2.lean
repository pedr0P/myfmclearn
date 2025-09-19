import Myfmclearn.ints.axioms

theorem B :
      ∀ (P Q R : Prop), ((P ∧ Q) → R) → ((P → Q) → R) ∨ (P → (Q → R))
    := by
      intro P Q R
      intro h
      right
      intro p
      intro q
      have : P ∧ Q := by
        constructor
        · exact p
        · exact q
      exact h this

theorem C1 :
      ∀ (a : Int), (-1) * a = -a
    := by
      intro a
      sorry
