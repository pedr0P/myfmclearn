section propositional

variable (P Q R : Prop)


------------------------------------------------
-- Double negation
------------------------------------------------

theorem doubleneg_intro :
  P → ¬ ¬ P  := by
  intro p
  intro np
  apply np p

theorem doubleneg_elim :
  ¬ ¬ P → P  := by
  intro nnp
  by_cases npop : P
  · exact npop
  · contradiction

theorem doubleneg_law :
  ¬ ¬ P ↔ P  := by
    exact ⟨doubleneg_elim P, doubleneg_intro P⟩

------------------------------------------------
-- Commutativity of ∨,∧
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  := by
    intro poq
    cases poq with
    | inl p =>
        right
        exact p
    | inr q =>
        left
        exact q


theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  := by
  intro peq
  exact ⟨peq.2, peq.1⟩


------------------------------------------------
-- Interdefinability of →,∨
------------------------------------------------

theorem impl_as_disj_converse :
  (¬ P ∨ Q) → (P → Q)  := by
  intro hnpoq p
  cases hnpoq with
  | inl np => contradiction
  | inr q => exact q

theorem disj_as_impl :
  (P ∨ Q) → (¬ P → Q)  := by
  intro hpoq
  intro np
  cases hpoq with
  | inl p => contradiction
  | inr q => exact q


------------------------------------------------
-- Contrapositive
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬ Q → ¬ P)  := by
    intro hpq
    intro nq
    intro p
    exact nq (hpq p)

theorem impl_as_contrapositive_converse :
  (¬ Q → ¬ P) → (P → Q)  := by
    intro nqnp
    intro p
    by_cases q : Q
    · exact q
    · specialize (nqnp q)
      contradiction

theorem contrapositive_law :
  (P → Q) ↔ (¬ Q → ¬ P)  := by
    exact ⟨impl_as_contrapositive P Q, impl_as_contrapositive_converse P Q⟩


------------------------------------------------
-- Irrefutability of LEM[P]
------------------------------------------------

-- CREDITS: Zulip discussion do Alvaro e Pedro Lúcio (e Thanos)
-- (Bobeei de novo)
theorem lem_irrefutable :
  ¬ ¬ (P ∨ ¬ P)  := by
    intro h
    have pnp1 : (P ∨ ¬ P) := by
      right
      intro p
      have pnp2 : (P ∨ ¬ P) := by
        left
        exact p
      exact h pnp2
    exact h pnp1
    


------------------------------------------------
-- Peirce's law
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬ ¬ P  := by
    intro h hp
    have this : (P → Q) := by
      intro p
      contradiction
    exact hp (h this)


------------------------------------------------
-- Linearity of →
------------------------------------------------

-- CREDITS: Zulip conversation do Pedro Lúcio com a Esther (e Thanos)!
-- (Fiquei preso nesse por um bom tempo e fiz bobera por não ter pedido ajuda.)
theorem impl_linear :
  (P → Q) ∨ (Q → P)  := by
    by_cases p : P
    · right
      intro q
      exact p
    · left
      intro pp
      contradiction

------------------------------------------------
-- Interdefinability of ∨,∧
------------------------------------------------

theorem disj_as_negconj :
  P ∨ Q → ¬ (¬ P ∧ ¬ Q)  := by
    intro h
    intro hn
    cases h with
    | inl l =>
        exact hn.1 l
    | inr r =>
        exact hn.2 r

theorem conj_as_negdisj :
  P ∧ Q → ¬ (¬ P ∨ ¬ Q)  := by
    intro h
    intro hn
    cases hn with
    | inl l =>
        exact l h.1
    | inr r =>
        exact r h.2


------------------------------------------------
-- De Morgan laws for ∨,∧
------------------------------------------------

theorem demorgan_disj :
  ¬ (P ∨ Q) → (¬ P ∧ ¬ Q)  := by
    intro h
    constructor
    · intro p
      have poq : (P ∨ Q) := by
        left
        exact p
      exact h poq
    · intro q
      have poq : (P ∨ Q) := by
        right
        exact q
      exact h poq

theorem demorgan_disj_converse :
  (¬ P ∧ ¬ Q) → ¬ (P ∨ Q)  := by
    intro h
    intro hn
    cases hn with
    | inr r =>
        exact h.2 r
    | inl l =>
        exact h.1 l
set_option pp.parens true
theorem demorgan_conj :
  ¬ (P ∧ Q) → (¬ Q ∨ ¬ P)  := by
    intro h
    by_cases q : Q
    · by_cases p : P
      · have this : (P ∧ Q) := by
          exact ⟨p, q⟩
        exfalso
        exact h this
      · right
        exact p
    · left
      exact q

theorem demorgan_conj_converse :
  (¬ Q ∨ ¬ P) → ¬ (P ∧ Q)  := by
    intro h
    intro hpeq
    cases h with
    | inl l =>
        exact l hpeq.2
    | inr r =>
        exact r hpeq.1

theorem demorgan_conj_law :
  ¬ (P ∧ Q) ↔ (¬ Q ∨ ¬ P)  := by
    exact ⟨demorgan_conj P Q, demorgan_conj_converse P Q⟩

theorem demorgan_disj_law :
  ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q)  := by
    exact ⟨demorgan_disj P Q, demorgan_disj_converse P Q⟩


------------------------------------------------
-- Distributivity laws between ∨,∧
------------------------------------------------

theorem distr_conj_disj :
  P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)  := by
    intro h
    obtain ⟨hl, hr⟩ := h
    cases hr with
    | inl l =>
        left
        exact ⟨hl, l⟩
    | inr r =>
        right
        exact ⟨hl, r⟩

theorem distr_conj_disj_converse :
  (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)  := by
    intro h
    cases h with
    | inl l =>
        constructor
        · exact l.1
        · left
          exact l.2
    | inr r =>
        constructor
        · exact r.1
        · right
          exact r.2

theorem distr_disj_conj :
  P ∨ (Q ∧ R) → (P ∨ Q) ∧ (P ∨ R)  := by
    intro h
    constructor
    · cases h with
      | inl l =>
          left
          exact l
      | inr r =>
          right
          exact r.1
    · cases h with
      | inl l =>
          left
          exact l
      | inr r =>
          right
          exact r.2


theorem distr_disj_conj_converse :
  (P ∨ Q) ∧ (P ∨ R) → P ∨ (Q ∧ R)  := by
    intro h
    obtain ⟨hl, hr⟩ := h
    cases hl with
    | inl l =>
        left
        exact l
    | inr r =>
        cases hr with
          | inl ll =>
            left
            exact ll
          | inr rr =>
            right
            constructor
            · exact r
            · exact rr



------------------------------------------------
-- Currying
------------------------------------------------

theorem curry_prop :
  ((P ∧ Q) → R) → (P → (Q → R))  := by
    intro h
    intro p
    intro q
    have this : (P ∧ Q) := by
      constructor
      · exact p
      · exact q
    exact h this

theorem uncurry_prop :
  (P → (Q → R)) → ((P ∧ Q) → R)  := by
    intro h
    intro hpeq
    apply h hpeq.1
    exact hpeq.2

    /- exact (h hpeq.1) hpeq.2 -/
------------------------------------------------
-- Reflexivity of →
------------------------------------------------

theorem impl_refl :
  P → P  := by
    intro p
    exact p

------------------------------------------------
-- Weakening and contraction
------------------------------------------------

theorem weaken_disj_right :
  P → (P ∨ Q)  := by
    intro p
    left
    exact p

theorem weaken_disj_left :
  Q → (P ∨ Q)  := by
    intro q
    right
    exact q

theorem weaken_conj_right :
  (P ∧ Q) → P  := by
    intro h
    exact h.1

theorem weaken_conj_left :
  (P ∧ Q) → Q  := by
    intro h
    exact h.2


------------------------------------------------
-- Idempotence of ∨,∧
------------------------------------------------

theorem disj_idem :
  (P ∨ P) ↔ P  := by
    constructor
    · intro pop
      cases pop with
      | inr r =>
          exact r
      | inl l =>
          exact l
    · intro p
      right
      exact p

theorem conj_idem :
  (P ∧ P) ↔ P := by
    constructor
    · intro pep
      exact pep.1
    · intro p
      constructor
      · exact p
      · exact p


------------------------------------------------
-- Bottom, Top
------------------------------------------------

theorem false_bottom :
  False → P := by
    exact False.elim

theorem true_top :
  P → True  := by
    intro p
    exact True.intro


end propositional

----------------------------------------------------------------

section predicate

variable (U : Type)
variable (P Q : U → Prop)


------------------------------------------------
-- De Morgan laws for ∃,∀
------------------------------------------------

theorem demorgan_exists :
  ¬ (∃ x, P x) → (∀ x, ¬ P x)  := by
    intro h
    intro x
    intro px
    have this : (∃ x, P x) := by
      exists x
    contradiction

theorem demorgan_exists_converse :
  (∀ x, ¬ P x) → ¬ (∃ x, P x)  := by
    intro h
    intro epx
    obtain ⟨x, xlegal⟩ := epx
    apply h x
    exact xlegal

theorem demorgan_forall :
  ¬ (∀ x, P x) → (∃ x, ¬ P x)  := by
    intro h
    by_cases m : (∃ x, ¬ P x)
    · exact m
    · have this: ¬ (∃ x, ¬ P x) → (∀ x, P x) := by
        intro h
        intro x
        false_or_by_contra
        have this: (∃ x, ¬ P x) := by
          exists x
        contradiction
      false_or_by_contra
      exact h (this m)

theorem demorgan_forall_converse :
  (∃ x, ¬ P x) → ¬ (∀ x, P x)  := by
    intro h
    intro oh
    obtain ⟨x, xlegal⟩ := h
    exact xlegal (oh x)


theorem demorgan_forall_law :
  ¬ (∀ x, P x) ↔ (∃ x, ¬ P x)  := by
    exact ⟨ demorgan_forall U P, demorgan_forall_converse U P⟩

theorem demorgan_exists_law :
  ¬ (∃ x, P x) ↔ (∀ x, ¬ P x)  := by
    exact ⟨ demorgan_exists U P, demorgan_exists_converse U P⟩

------------------------------------------------
-- Interdefinability of ∃,∀
------------------------------------------------

theorem exists_as_neg_forall :
  (∃ x, P x) → ¬ (∀ x, ¬ P x)  := by
    intro h
    intro oh
    obtain ⟨x, px⟩ := h
    exact (oh x) px

theorem forall_as_neg_exists :
  (∀ x, P x) → ¬ (∃ x, ¬ P x)  := by
    intro h
    intro oh
    obtain ⟨x, px⟩ := oh
    exact px (h x)

theorem forall_as_neg_exists_converse :
  ¬ (∃ x, ¬ P x) → (∀ x, P x)  := by
    intro h
    intro x
    false_or_by_contra
    have : (∃ x, ¬ P x) := by
      exists x
    contradiction
    
theorem exists_as_neg_forall_converse :
  ¬ (∀ x, ¬ P x) → (∃ x, P x)  := by
    intro nhan
    by_cases mm : (∃ x, P x)
    · exact mm
    · exfalso
      exact nhan (demorgan_exists U P mm)


theorem forall_as_neg_exists_law :
  (∀ x, P x) ↔ ¬ (∃ x, ¬ P x)  := by
    exact ⟨ forall_as_neg_exists U P, forall_as_neg_exists_converse U P ⟩

theorem exists_as_neg_forall_law :
  (∃ x, P x) ↔ ¬ (∀ x, ¬ P x)  := by
    exact ⟨ exists_as_neg_forall U P, exists_as_neg_forall_converse U P ⟩

------------------------------------------------
--  Distributivity between quantifiers
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃ x, P x ∧ Q x) → (∃ x, P x) ∧ (∃ x, Q x)  := by
    intro h
    constructor
    · obtain ⟨x, peq⟩ := h
      obtain ⟨l,r⟩ := peq
      exists x 
    · obtain ⟨x, peq⟩ := h
      obtain ⟨l,r⟩ := peq
      exists x 

theorem exists_disj_as_disj_exists :
  (∃ x, P x ∨ Q x) → (∃ x, P x) ∨ (∃ x, Q x)  := by
    intro h
    obtain ⟨x, poq⟩ := h
    rcases poq with l|r
    · left
      exists x
    · right
      exists x

theorem exists_disj_as_disj_exists_converse :
  (∃ x, P x) ∨ (∃ x, Q x) → (∃ x, P x ∨ Q x)  := by
    intro h
    rcases h with l|r
    · obtain ⟨x,px⟩ := l
      exists x
      left
      exact px
    · obtain ⟨x,qx⟩ := r
      exists x
      right
      exact qx

theorem forall_conj_as_conj_forall :
  (∀ x, P x ∧ Q x) → (∀ x, P x) ∧ (∀ x, Q x)  := by
    intro h
    constructor
    · intro x
      specialize h x
      exact h.1
    · intro x
      specialize h x
      exact h.2

theorem forall_conj_as_conj_forall_converse :
  (∀ x, P x) ∧ (∀ x, Q x) → (∀ x, P x ∧ Q x)  := by
    intro h
    intro x
    obtain ⟨px,qx⟩ := h
    constructor
    · exact px x
    · exact qx x

theorem forall_disj_as_disj_forall_converse :
  (∀ x, P x) ∨ (∀ x, Q x) → (∀ x, P x ∨ Q x)  := by
    intro h
    intro x
    rcases h with l|r
    · left
      exact l x
    · right
      exact r x

end predicate

------------------------------------------------

section bonus

------------------------------------------------
--  Drinker's paradox
------------------------------------------------

variable (D : U → Prop)

-- There is a person p such that:
-- if p drinks, then everybody drinks
-- p: «person»
-- D x: «x drinks»
theorem drinker :
  ∃ p, (D p → ∀ x, D x)  := by
    have : ¬(∃ p, (D p → ∀ x, ¬ D x)) := by
      intro h
      obtain ⟨x, dx⟩ := h
      sorry

------------------------------------------------
--  Russell's paradox
------------------------------------------------

variable (S : U → U → Prop)

-- It is impossible to have a barber b such that
-- b shaves exactly those people who do not shave themselves
-- b: «barber»
-- S x y: «x shaves y»
theorem russell :
  ¬ ∃ b, ∀ x, (S b x ↔ ¬ S x x)  := by
    intro h
    obtain ⟨l, r⟩ := h
    sorry





end bonus


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀ x, P x ∨ Q x) → (∀ x, P x) ∨ (∀ x, Q x)  := by
  sorry

theorem exists_conj_as_conj_exists_converse :
  (∃ x, P x) ∧ (∃ x, Q x) → (∃ x, P x ∧ Q x)  := by
  sorry

---------------------------------------------- -/
