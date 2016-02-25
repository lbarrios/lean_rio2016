open classical
variables (A : Type)(p q : A → Prop)
variable r: Prop

--------------
-- example 1
--------------
example: (∃x, p x ∨ q x) ↔ (∃x, p x) ∨ (∃x, q x) := sorry

--------------
-- example 2
--------------
example: (¬∀x, p x) ↔ (∃x, ¬ p x) := sorry

--------------
-- example 3
--------------
example: (∃x, p x) ↔ ¬ (∀x, ¬ p x) := sorry

--------------
-- example 4
--------------
example: (a: A) : (∃x, r → p x) ↔ (r → ∃x, p x) := sorry

--------------
-- example 5
--------------
example: (∃x: A, true) → (∀x, p x ∧ r) → (∀x, p x) ∧ r := sorry
