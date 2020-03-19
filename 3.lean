/-
  Exercise 1.
    Prove the following identities, replacing the “sorry” placeholders with actual proofs.
-/

variables p q r : Prop

-- commutativity of ∧ and ∨

theorem and_com {p q : Prop} : p ∧ q ↔ q ∧ p := 
iff.intro
  (assume h : p ∧ q,
    show q ∧ p, from ⟨ h.right, h.left ⟩)
  (assume h : q ∧ p,
    show p ∧ q, from ⟨ h.right, h.left ⟩)
  
theorem or_com {p q : Prop} : p ∨ q ↔ q ∨ p :=
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

theorem and_ass {p q r : Prop} : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume h : (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from ⟨ h.left.left, ⟨ h.left.right, h.right ⟩ ⟩)
  (assume h : p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from ⟨ ⟨ h.left, h.right.left ⟩, h.right.right ⟩)

theorem or_ass {p q r : Prop} : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
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

theorem exportation {p q r : Prop} : (p → (q → r)) ↔ (p ∧ q → r) :=
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

theorem nonabsurdity : ¬(p ∧ ¬p) := 
assume h : p ∧ ¬p,
absurd h.left h.right

example : p ∧ ¬q → ¬(p → q) :=
assume (h₁ : p ∧ ¬q) (h₂ : p → q),
absurd (h₂ h₁.left) h₁.right

-- principle of explosion
theorem explosion : ¬p → (p → q) := 
assume (hnp : ¬p) (hp : p),
absurd hp hnp

-- material implication
theorem mat_impl_right {p q : Prop} : (¬p ∨ q) → (p → q) := 
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
(em p).elim
  (assume hp : p,
    show false, from absurd hp (h.mp hp))
  (assume hnp : ¬p,
    show false, from absurd (h.mpr hnp) hnp)

example : (p → q) → (¬q → ¬p) := 
assume (hpq : p → q) (hnq : ¬q) (hp : p),
show false, from hnq (hpq hp)



/-
  Exercise 2.
    Prove the following identities, replacing the “sorry” placeholders with actual proofs.
    These require classical reasoning.
-/

open classical

theorem mat_impl_left {p q : Prop} : (p → q) → (¬p ∨ q) :=
assume h : p → q,
by_cases
  (assume hp : p,
    or.inr (h hp))
  (assume hnp : ¬p,
    or.inl hnp)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
assume h : p → q ∨ r,
have h₁ : ¬p ∨ (q ∨ r), from mat_impl_left h,
have h₂ : (¬p ∨ q) ∨ r, from or_ass.elim_right h₁,
have h₃ : r ∨ (¬p ∨ q), from or_com.elim_left h₂,
have h₄ : ¬p ∨ (r ∨ (¬p ∨ q)), from or.inr h₃,
have h₅ : (¬p ∨ r) ∨ (¬p ∨ q), from or_ass.elim_right h₄,
h₅.elim
  (assume hh : (¬p ∨ r),
    have ha : p → r, from mat_impl_right hh,
    or.inr ha)
  (assume hh : (¬p ∨ q),
    have ha : p → q, from mat_impl_right hh,
    or.inl ha)

theorem demorgans_4 {p q : Prop} : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume h : ¬(p ∧ q),
by_cases
  (assume hp : p, by_cases
    (assume hq : q, absurd (and.intro hp hq) h)
    (assume hnq : ¬q, or.inr hnq))
  (assume hnp : ¬p, or.inl hnp)

theorem dne {p : Prop} (h : ¬¬p) : p :=
or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

-- probably could use mat_impl_left and demorgans
theorem mat_impl_neg_left {p q : Prop} : ¬(p → q) → p ∧ ¬q :=
assume h : ¬(p → q),
by_contradiction
  (assume hc : ¬(p ∧ ¬q),
    have h₁ : ¬p ∨ ¬¬q, from demorgans_4 hc,
    have h₂ : ¬p ∨ q, from h₁.elim
      (assume g : ¬p, or.inl g)
      (assume g : ¬¬q, or.inr (dne g)),
    have h₃ : p → q, from mat_impl_right h₂,
    show false, from h h₃)

-- example : (p → q) → (¬p ∨ q) := sorry -- proved above as theorem mat_impl_left

example : (¬q → ¬p) → (p → q) :=
assume (h : ¬q → ¬p) (hp : p),
by_cases
  (assume hq : q, hq)
  (assume hnq : ¬q, absurd hp (h hnq))

example : p ∨ ¬p := em p

-- Peirce's law
example : (((p → q) → p) → p) :=
assume h : (p → q) → p,
by_cases
  (assume hc : p → q, h hc)
  (assume hc : ¬(p → q),
    have h₁ : p ∧ ¬q, from mat_impl_neg_left hc,
    h₁.left)

/-
  Exercise 3.
    Prove ¬(p ↔ ¬p) without using classical logic.
-/

example : ¬(p ↔ ¬p) :=
assume h,
have h₁ : p → ¬p, from h.elim_left,
have h₂ : ¬p → p, from h.elim_right,
have h₃ : ¬(p ∧ p), from exportation.elim_left h₁,
have hnp : ¬p, from sorry, -- so close...
absurd (h₂ hnp) hnp
