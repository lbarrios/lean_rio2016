-------------------------------------------------------
-- Question 4. Prove that every relation R 
-- which is transitive, symmetric and serial
-- is also reflexive.
-- Replace the 'sorry' placeholder by an actual proof.
-------------------------------------------------------

variable A : Type
variable R : A → A → Prop

premise transitive : ∀ {a b c : A},
  R a b → R b c → R a c

premise symmetric : ∀ {a b : A},
  R a b → R b a

premise serial : ∀ a : A, ∃ b : A,
  R a b

lemma refl : ∀ a, R a a := sorry
