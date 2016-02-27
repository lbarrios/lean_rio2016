-------------------------------------------------------
-- Question 3: Prove the equality type defined below
-- is symmetric, transitive ad congruent.
-- Replace the 'sorry' placeholders by actual proofs.
-------------------------------------------------------

inductive Eq {A : Type} (a : A) : A → Prop :=
Refl : Eq a a

theorem Subst {A : Type} (a b : A) {P : A → Prop}
  (H₁ : Eq a b)(H₂ : P a) : P b :=
Eq.rec H₂ H₁

theorem Symm {A : Type} {a b : A} (H : Eq a b) : Eq b a := sorry
theorem Trans {A : Type} {a b c : A} (H₁ : Eq a b) (H₂ : Eq b c) : Eq a c := sorry
theorem Congr {A B : Type} {a b : A} (f : A → B) (H : Eq a b) : Eq (f a) (f b) := sorry
