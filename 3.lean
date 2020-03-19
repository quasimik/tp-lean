/-
  Exercise 1.
    Prove the following identities, replacing the “sorry” placeholders with actual proofs.
-/

variables p q r : Prop

-- commutativity of ∧ and ∨

example : p ∧ q ↔ q ∧ p := 
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from ⟨ h.right, h.left ⟩)
  (assume h : q ∧ p,
    show p ∧ q, from ⟨ h.right, h.left ⟩)
  
example : p ∨ q ↔ q ∨ p :=
iff.intro
  (assume h : p ∨ q,
    h.elim
      (assume hp : p, or.inr hp)
      (assume hq : q, or.inl hq))
  (assume h : q ∨ p,
    h.elim
      (assume hq : q, or.inr hq)
      (assume hp : p, or.inl hp))

-- associativity of ∧ and ∨

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume h : (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from ⟨ h.left.left, ⟨ h.left.right, h.right ⟩ ⟩)
  (assume h : p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from ⟨ ⟨ h.left, h.right.left ⟩, h.right.right ⟩)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (assume h : (p ∨ q) ∨ r,
    h.elim
    (assume hpq : p ∨ q,
      hpq.elim
      (assume hp : p,
        show p ∨ (q ∨ r), from or.inl hp)
      (assume hq : q,
        show p ∨ (q ∨ r), from or.inr (or.inl hq)))
    (assume hr : r,
      show p ∨ (q ∨ r), from or.inr (or.inr hr)))
  (assume h : p ∨ (q ∨ r),
    h.elim
    (assume hp : p,
      show (p ∨ q) ∨ r, from or.inl (or.inl hp))
    (assume hqr : q ∨ r,
      hqr.elim
      (assume hq : q,
        show (p ∨ q) ∨ r, from or.inl (or.inr hq))
      (assume hr : r,
        show (p ∨ q) ∨ r, from or.inr hr)))

-- distributivity

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    h.right.elim
      (assume hq : q,
        show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨ h.left, hq ⟩)
      (assume hr : r,
        show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨ h.left, hr ⟩))
  (assume h : (p ∧ q) ∨ (p ∧ r),
    h.elim
      (assume hpq : p ∧ q,
        show p ∧ (q ∨ r), from ⟨ hpq.left, or.inl hpq.right ⟩)
      (assume hpr : p ∧ r,
        show p ∧ (q ∨ r), from ⟨ hpr.left, or.inr hpr.right ⟩))
      

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
  (assume h : p ∨ (q ∧ r),
    h.elim
      (assume hp : p,
        show (p ∨ q) ∧ (p ∨ r), from ⟨ or.inl hp, or.inl hp ⟩)
      (assume hqr : q ∧ r,
        show (p ∨ q) ∧ (p ∨ r), from ⟨ or.inr hqr.left, or.inr hqr.right ⟩))
  (assume h : (p ∨ q) ∧ (p ∨ r),
    have hpq : p ∨ q, from h.left,
    have hpr : p ∨ r, from h.right,
    hpq.elim
      (assume hp : p,
        show p ∨ (q ∧ r), from or.inl hp)
      (assume hq : q,
        hpr.elim
          (assume hp : p,
            show p ∨ (q ∧ r), from or.inl hp)
          (assume hr : r,
            show p ∨ (q ∧ r), from or.inr ⟨ hq, hr ⟩)))

-- other properties

example : (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
  (assume (h₁ : (p → q → r)) (h₂ : p ∧ q),
    show r, from h₁ h₂.left h₂.right)
  (assume (h : p ∧ q → r) (hp : p) (hq : q),
    show r, from h (and.intro hp hq))

theorem antidist_or : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
  (assume (h₁ : p ∨ q → r),
    show (p → r) ∧ (q → r), from and.intro -- ⟨ λ hp, h₁ (or.inl hp), λ hq, h₁ (or.inr hq) ⟩
      (assume hp : p,
        have h₂ : p ∨ q, from or.inl hp,
        show r, from h₁ h₂)
      (assume hq : q,
        have h₂ : p ∨ q, from or.inr hq,
        show r, from h₁ h₂))
  (assume (h₁ : (p → r) ∧ (q → r)) (h₂ : p ∨ q),
    show r, from h₂.elim
      (assume hp : p, h₁.left hp)
      (assume hq : q, h₁.right hq))

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := antidist_or p q false

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
assume (h₁ : ¬p ∨ ¬q) (h₂ : p ∧ q),
h₁.elim
  (assume hnp : ¬p, absurd h₂.left hnp)
  (assume hnq : ¬q, absurd h₂.right hnq)

-- nonabsurdity
example : ¬(p ∧ ¬p) := 
assume h : p ∧ ¬p,
absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
assume (h₁ : p ∧ ¬q) (h₂ : p → q),
absurd (h₂ h₁.left) h₁.right

-- explosion
example : ¬p → (p → q) := 
assume (hnp : ¬p) (hp : p),
absurd hp hnp

example : (¬p ∨ q) → (p → q) := 
assume (h : ¬p ∨ q) (hp : p),
h.elim
  (assume hnp : ¬p, absurd hp hnp)
  (assume hq : q, hq)

example : p ∨ false ↔ p := 
iff.intro
  (assume h : p ∨ false, h.elim
    (assume hp : p, hp)
    (assume hf : false, hf.elim))
  (assume hp : p, or.inl hp)

example : p ∧ false ↔ false := 
iff.intro
  (assume h : p ∧ false, h.right.elim)
  (assume h : false, h.elim)

open classical

example : ¬(p ↔ ¬p) := 
assume h,
or.elim (em p)
  (assume hp : p,
    show false, from absurd hp (h.mp hp))
  (assume hnp : ¬p,
    show false, from absurd (h.mpr hnp) hnp)

example : (p → q) → (¬q → ¬p) := 
assume (hpq : p → q) (hnq : ¬q) (hp : p),
show false, from hnq (hpq hp)

