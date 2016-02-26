open classical
variables (A : Type)(p q : A → Prop)
variable r: Prop

--------------
-- example 1
--------------
example: (∃x, p x ∨ q x) ↔ (∃x, p x) ∨ (∃x, q x) := 
iff.intro
    (assume H : ∃x, p x ∨ q x,
    obtain x₁ H₁, from H,
    show (∃x, p x) ∨ (∃x, q x), from or.elim H₁ 
        (assume Hx₁ : p x₁,
        or.inl (exists.intro x₁ Hx₁))
        (assume Hx₁ : q x₁, 
        or.inr (exists.intro x₁ Hx₁)))
    (assume Q : (∃x, p x) ∨ (∃x, q x),
    or.elim Q
        (assume P : (∃x, p x),
        obtain x₁ P₁, from P,
        exists.intro x₁ (or.inl P₁))
        (assume Q : (∃x, q x),
        obtain x₁ Q₁, from Q,
        exists.intro x₁ (or.inr Q₁)))

--------------
-- example 2
--------------
example: (¬∀x, p x) ↔ (∃x, ¬ p x) := 
iff.intro
    (assume nH : ¬(∀x, p x),
    show (∃x, ¬ p x), from or.elim (em (∃x, ¬ p x))
        (assume Qn : (∃x, ¬ p x), Qn)
        (assume nQn : ¬(∃x, ¬ p x),
        have Hnn : (∀x, ¬¬p x), from
            (take x,
            assume nP : ¬ p x,
            have Qn: (∃x, ¬ p x), from exists.intro x nP,
            show false, from nQn Qn),
        have H : (∀x, p x), from 
            (take x,
            have nnP : ¬¬p x, from Hnn x,
            have P : p x, from or.elim (em (p x))
                (assume P, P)
                (assume nP : ¬p x,
                absurd nP (Hnn x)),
            P),
        absurd H nH))
    (assume Qn : (∃x, ¬ p x),
    obtain x₁ (Qn₁ : ¬ p x₁), from Qn,
    show (¬∀x, p x), from not.intro (
        assume H: (∀x, p x),
        show false, from not.elim (Qn₁) (H x₁)))

--------------
-- example 3
--------------
example: (∃x, p x) ↔ ¬ (∀x, ¬ p x) := sorry

--------------
-- example 4
--------------
example (a: A) : (∃x, r → p x) ↔ (r → ∃x, p x) := sorry

--------------
-- example 5
--------------
example: (∃x: A, true) → (∀x, p x ∧ r) → (∀x, p x) ∧ r := sorry
