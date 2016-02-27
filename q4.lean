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

lemma refl : ∀ a, R a a :=
  have H₁ : (∀ a:A, ∃ b:A, R a b), from serial,
  take a₁ : A,
  have H₂ : ∃ b : A, R a₁ b, from (H₁ a₁),
  obtain b₁ (H₃ : R a₁ b₁), from H₂,
  have H₄ : R b₁ a₁, from symmetric H₃,
  have H₅ : R a₁ a₁, from transitive H₃ H₄,
  H₅
