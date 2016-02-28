# Lean Theorem Prover
## Escuela de Verano de Rio Cuarto - 2016

Repository for the solutions to the assignments for the course ["The Lean Theorem Prover"](https://leanprover.github.io/) from ["Escuela de Verano de Rio Cuarto"](http://dc.exa.unrc.edu.ar/rio2016/) (February 2016).

### Guidelines
* Tactics must not be used to solve the problems.
* Create a separate `.lean` file for each question.
* Make sure the `.lean` files type check.
* Partial solutions can be submitted using 'sorry'.

### Exercises

##### Question 1. 
Prove the following assertions in propositional logic. Prove as many as you can, to replace the 'sorry' placeholders by actual proofs. Some of then require classical reasoning.

```lean
open classical
variables p q r s: Prop

example: p ∧ (q∨r) ↔ (p∧q) ∨ (p∧r) := sorry

example: ¬p∨¬q → ¬(p∧q) := sorry

example: (¬q → ¬p) → (p → q) := sorry

example: (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
```
##### Question 2.
Prove the following four identities, and determine are nonconstructive, and hence require some form of classical reasoning. Replace the 'sorry' placeholders by actual proofs.

```lean
open classical
variables (A : Type)(p q : A → Prop)
variable r: Prop

example: (∃x, p x ∨ q x) ↔ (∃x, p x) ∨ (∃x, q x) := sorry

example: (¬∀x, p x) ↔ (∃x, ¬ p x) := sorry

example: (∃x, p x) ↔ ¬ (∀x, ¬ p x) := sorry

example (a: A) : (∃x, r → p x) ↔ (r → ∃x, p x) := sorry

example: (∃x: A, true) → (∀x, p x ∧ r) → (∀x, p x) ∧ r := sorry
```

##### Question 3. 
Prove the equality type defined below is symmetric, transitive ad congruent. Replace the 'sorry' placeholders by actual proofs.

```lean
inductive Eq {A : Type} (a : A) : A → Prop := sorry

theorem Subst {A : Type} {a b : A} {P : A → Prop} (H₁ : Eq a b)(H₂ : P a) : P b := sorry

theorem Symm {A : Type} {a b : A} (H : Eq a b) : Eq b a := sorry

theorem Trans {A : Type} {a b c : A} (H₁ : Eq a b) (H₂ : Eq b c) : Eq a c := sorry

theorem Congr {A B : Type} {a b : A} (f : A → B) (H : Eq a b) : Eq (f a) (f b) := sorry
```

##### Question 4.
Prove that every relation R which is transitive, symmetric and serial is also reflexive. Replace the 'sorry' placeholder by an actual proof.

```lean
variable A : Type
variable R : A → A → Prop

premise transitive : ∀ {a b c : A},
  R a b → R b c → R a c

premise symmetric : ∀ {a b : A},
  R a b → R b a

premise serial : ∀ a : A, ∃ b : A,
  R a b

lemma refl : ∀ a, R a a := sorry
```
