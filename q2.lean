/-
Question 2. Prove the following four identities, and determine are nonconstructive,
and hence require some form of classical reasoning.
Replace the 'sorry' placeholders by actual proofs.
-/
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
example: (∃x, p x) ↔ ¬ (∀x, ¬ p x) :=
iff.intro
    (assume H : (∃x, p x),
    obtain x₁ H₁, from H,
    not.intro ( assume Qn: (∀x, ¬p x),
        not.elim (Qn x₁) H₁))
    (assume nQn : ¬ (∀x, ¬p x),
    show (∃x, p x), from or.elim (em (∃x, p x))
        (assume H : (∃x, p x), H)
        (assume nH : ¬(∃x, p x),
        have Qn : (∀x, ¬p x), from
            (take x,
            assume P : p x,
            have H: (∃x, p x), from exists.intro x P,
            show false, from nH H),
        absurd Qn nQn))

--------------
-- example 4
--------------
example (a: A) : (∃x, r → p x) ↔ (r → ∃x, p x) := 
iff.intro
    (assume P: (∃x, r → p x),
    obtain x (Hrpx: r → p x), from P,
    assume Hr : r,
    have Hpx: p x, from Hrpx Hr,
    exists.intro x Hpx)
    (assume Q : r → (∃x, p x),
    show ∃x, r → p x, from or.elim (em r)
        (assume Hr: r,
        have eHpx: (∃x, p x), from Q Hr,
        obtain x Hpx, from eHpx,
        have Hrpx : r → p x, from
            (assume r, Hpx),
        exists.intro x Hrpx)
        (assume Hnr: ¬r,
        have fP : (∀x, r → p x), from 
            (take x: A,
            assume Hr: r,
            absurd Hr Hnr),
        exists.intro a (
            assume Hr: r,
            have Hpa : p a, from (fP a Hr),
            Hpa)))

--------------
-- example 5
--------------
example: (∃x: A, true) → (∀x, p x ∧ r) → (∀x, p x) ∧ r :=
assume H₁ : (∃x: A, true),
assume H₂ : (∀x, p x ∧ r),
obtain x₀ T₀, from H₁,
have H₃ : p x₀ ∧ r, from H₂ x₀,
have Hpx : p x₀, from and.left H₃,
have Hr : r, from and.right H₃,
have Hapx : (∀x, p x), from 
    (take x, and.left (H₂ x)),
show (∀x, p x) ∧ r, from and.intro Hapx Hr
