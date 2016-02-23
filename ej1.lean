open classical
variables p q r s: Prop

example: p ∧ (q∨r) ↔ (p∧q) ∨ (p∧r) := 
iff.intro
-- proof of →:
(assume H₁ : p ∧ (q∨r),
    have Hp : p, from and.left H₁,
    have Hqvr : (q∨r), from and.right H₁,
    or.elim Hqvr
        (assume Hq: q,
            -- if q, then p∧q, then (p∧q) ∨ any
            show (p∧q) ∨ (p∧r), from or.intro_left (p∧r) (and.intro Hp Hq))
        (assume Hr: r,
            -- if r, then p∧r, then (p∧r) ∨ any
            show (p∧q) ∨ (p∧r), from or.intro_right (p∧q) (and.intro Hp Hr))
)
-- proof of ←:
(assume H₂ : (p∧q) ∨ (p∧r),
    -- proof of p
    have Hp : p, from or.elim H₂ 
        (assume Hpyq : p∧q,
        show p, from and.left Hpyq)
        (assume Hpyr : p∧r,
        show p, from and.left Hpyr),
    -- proof of q∨r
    have Hqvr: (q∨r), from or.elim H₂
        (assume Hpq : (p∧q),
        show (q∨r), from or.intro_left r (and.elim_right Hpq))
        (assume Hpr : (p∧r),
        show (q∨r), from or.intro_right q (and.elim_right Hpr)),
    -- conjunction
    show p ∧ (q∨r), from and.intro Hp Hqvr)

example: ¬p∨¬q → ¬(p∧q) :=
assume H : ¬p∨¬q,
show ¬(p∧q), from or.elim H
    (assume Hnp : ¬p,
    show ¬(p∧q), from or.elim (em (p∧q))
        (assume Hpq : p∧q, absurd (and.left Hpq) Hnp)
        (assume Hnpq : ¬(p∧q), Hnpq))
    (assume Hnq : ¬q,
    show ¬(p∧q), from or.elim (em (p∧q))
        (assume Hpq : p∧q, absurd (and.right Hpq) Hnq)
        (assume Hnpq : ¬(p∧q), Hnpq))