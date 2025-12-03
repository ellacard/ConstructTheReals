import ConstructTheReals.Field
import ConstructTheReals.Order

/-

Defines localization of a commutative monoid, as well as extensions to rings.

- Given a commutative monoid M and a submonoid S, define the localization M / S.
- When S = M then we get the group of differences of M.

For rings, there are additive/multiplicative variants of the localization.

1. Additive localization (group of differences):
  - Equivalence: (a₁, b₁) ≃ (a₂, b₂) := ∃ k, a₁ + b₂ + k = a₂ + b₁ + k

  - Addition: (a₁ - b₁) + (a₂ - b₂) := (a₁ + a₂) - (b₂ + b₂)

  - Multiplication: (a₁ - b₁) * (a₂ - b₂) = (a₁a₂ + b₁b₂) - (a₁b₂ + a₂b₁)

2. Multiplicative localization:
  - Equivalence: (a₁, b₁) ≃ (a₂, b₂) := ∃ k, k * (a₁ * b₂ - a₂ * b₁) = 0

                          equivalently, ∃ k, a₁ * b₂ * k = a₂ * b₁ * k

  - Multiplication: (a₁ / b₁) * (a₂ / b₂) := (a₁ * a₂) / (b₁ * b₂)

  - Addition: (a₁ / b₁) + (a₂ / b₂) = (a₁b₂ + a₂b₁) / (b₁b₂)

In the former case, multiplication is called the "upper" operation
in the latter, addition is called the "lower" operation.

TODO:
- How to systematically lift order structure?
- (Subobject) Construct an embedding R -> R/S sending x to (x, unit).
- (Idempotence) Prove if G is already a group then G/G is isomorphic to G.
- Prove if S = R then the multiplicative localization is the trivial ring
  (since 0 is given an inverse, then 1 = 0 * 0⁻¹ = 0 → 0 = 1)

-/

namespace Localization

section Monoid

variable {α: Type u} [M: CommMonoid α] {β: Set α}

open Monoid

-- Define the localization relation on α × β.

def relation (β: Set α): α × β → α × β → Prop :=
  λ (a₁, ⟨a₂, _⟩) (b₁, ⟨b₂, _⟩) ↦ ∃ t ∈ β, a₁ + b₂ + t = b₁ + a₂ + t

instance: HasEquiv (α × β) := {
  Equiv := relation β
}

-- Prove it is an equivalence relation.

theorem equivalence (h: M.sub β): Equivalence (relation β) := {
  refl := by
    intro
    exists 0
    constructor
    · exact h.unit_mem
    ·  rw [op_unit_right]
  symm := by
    intro _ _ ⟨t, ht₁, ht₂⟩
    exists t
    constructor
    · exact ht₁
    · exact Eq.symm ht₂
  trans := by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
    exists t₁ + t₂ + b₂
    constructor
    · repeat apply h.op_closed
      · exact ht₁₁
      · exact ht₂₁
      · exact b₂.property
    · calc
        a₁ + c₂ + (t₁ + t₂ + b₂)
        _ = (a₁ + b₂ + t₁) + c₂ + t₂ := by simp_monoid
        _ = (b₁ + a₂ + t₁) + c₂ + t₂ := by rw [ht₁₂]
        _ = a₂ + t₁ + (b₁ + c₂ + t₂) := by simp_monoid
        _ = a₂ + t₁ + (c₁ + b₂ + t₂) := by rw [ht₂₂]
        _ = c₁ + a₂ + (t₁ + t₂ + b₂) := by simp_monoid
}

-- Define the quotient.

def setoid (h: M.sub β): Setoid (α × β) := {
  r := relation β
  iseqv := equivalence h
}

def quotient (h: M.sub β): Type u :=
  Quotient (setoid h)

def quotient.unit (h: M.sub β): quotient h :=
  Quotient.mk _ (0, ⟨0, h.unit_mem⟩)

-- Lift the operation to the quotient.
-- First define the operation on α × β.

def quotient.op_pre (h: M.sub β): Op (α × β) :=
  λ (a₁, ⟨a₂, h₁⟩) (b₁, ⟨b₂, h₂⟩) ↦ (a₁ + b₁, ⟨a₂ + b₂, h.op_closed a₂ b₂ h₁ h₂⟩)

-- Then prove it is well defined on the quotient,
-- i.e. if a ≈ c and b ≈ d, then a + b ≈ c + d.

theorem quotient.op_lifts (h: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.op_pre h a b) = Quotient.mk (setoid h) (quotient.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ + t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · calc
      a₁ + b₁ + (c₂ + d₂) + (t₁ + t₂)
      _ = (a₁ + c₂ + t₁) + (b₁ + d₂ + t₂) := by simp_monoid
      _ = (c₁ + a₂ + t₁) + (d₁ + b₂ + t₂) := by rw [ht₁₂, ht₂₂]
      _ = c₁ + d₁ + (a₂ + b₂) + (t₁ + t₂) := by simp_monoid

def quotient.op (h: M.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.op_lifts h)

-- Show α / β is a commutative monoid.

instance Localization (h: M.sub β): CommMonoid (quotient h) := {
  unit := quotient.unit h
  op := quotient.op h
  identity := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
      constructor
      exact h.unit_mem
    )
    simp [op_unit_left]
    simp [op_unit_right]
  assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intros
    apply Quotient.sound
    exists 0
    constructor
    · exact h.unit_mem
    · simp [op_assoc]
  comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intros
    apply Quotient.sound
    exists 0
    constructor
    · exact h.unit_mem
    · simp [op_comm]
}



-- Define the localization of a commutative monoid at the full set,
-- i.e. the group of differences.

def setoid.full: Setoid (α × @Set.full α) :=
  setoid M.full_sub

abbrev quotient.full (α: Type u) [M: CommMonoid α]: Type u :=
  quotient M.full_sub

-- Define the additive inverse operation on α × β.

def quotient.inv_pre: α × @Set.full α → α × @Set.full α :=
  λ (a₁, a₂) ↦ (a₂, ⟨a₁, by trivial⟩)

-- Prove if a ≈ b, then -a ≈ -b

theorem quotient.inv.lifts: ∀ a b: α × @Set.full α, a ≈ b → Quotient.mk setoid.full (quotient.inv_pre a) = Quotient.mk setoid.full (quotient.inv_pre b) := by
  intro (a₁, ⟨a₂, h₁⟩) (b₁, ⟨b₂, h₂⟩) ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · trivial
  · calc
      a₂ + b₁ + t
      _ = b₁ + a₂ + t := by simp_monoid
      _ = a₁ + b₂ + t := by rw [ht₂]
      _ = b₂ + a₁ + t := by simp_monoid

def quotient.inv: quotient.full (α := α) → quotient.full (α := α) :=
  λ x ↦ Quotient.liftOn x _ quotient.inv.lifts

-- Show α / α is a commutative group.

def Localization.group_of_differences: CommGroup (quotient.full α) := {
  inv := quotient.inv
  inverse := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro (a, ⟨b, hb⟩)
      apply Quotient.sound
      exists 0
      constructor
      · trivial
      · simp [op_unit_right, op_comm]
    )
}

end Monoid



section Additive

variable {α: Type u} [R: Semiring α] {β: Set α}

-- Additive localization of a semiring.

-- Define the upper operation "multiplication" on α × β.
-- Note that this requires β to be an ideal.

def quotient.upper.op_pre (h: R.ideal β): Op (α × β) :=
  λ (a₁, ⟨a₂, h₁⟩) (b₁, ⟨b₂, h₂⟩) ↦ (a₁ * b₁ + a₂ * b₂, ⟨a₁ * b₂ + b₁ * a₂, by {
    apply h.op_closed
    · exact h.absorb_prod_right b₂ a₁ h₂
    · exact h.absorb_prod_right a₂ b₁ h₁
  }⟩)

-- Prove if a ≈ c and b ≈ d, then a * b ≈ c * d.

theorem quotient.upper.op_lifts (h: R.ideal β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h.toSubmonoid) (quotient.upper.op_pre h a b) = Quotient.mk (setoid h.toSubmonoid) (quotient.upper.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  let t: α := sorry
  let stuff: α := sorry
  let other_stuff: α := sorry
  exists t
  constructor
  · sorry
  · calc
      a₁ * b₁ + a₂ * b₂ + (c₁ * d₂ + d₁ * c₂) + t
      _ = c₁ * d₁ + c₂ * d₂ + (a₁ * b₂ + b₁ * a₂) + t := by sorry

def quotient.upper.op (h: R.ideal β): Op (quotient h.toSubmonoid) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.upper.op_lifts h)

-- Prove that the localization of a commutative semiring wrt. addition is a semiring.
-- TODO need CommSemiring for mul_assoc?

instance Localization.additive [R: Semiring α] (h: R.ideal β): Semiring (quotient h.toSubmonoid) := {
  add       := (Localization h.toSubmonoid).op
  zero      := (Localization h.toSubmonoid).unit
  add_assoc := (Localization h.toSubmonoid).assoc
  add_zero  := (Localization h.toSubmonoid).identity
  add_comm  := (Localization h.toSubmonoid).comm
  mul       := quotient.upper.op h
  one       := Quotient.mk _ (1, ⟨0, h.unit_mem⟩)
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    apply Quotient.sound
    exists 0
    constructor
    · exact h.unit_mem
    · repeat rw [add_zero_right]
      calc
        (a₁ * b₁ + a₂ * b₂) * c₁ + (a₁ * b₂ + b₁ * a₂) * c₂ + (a₁ * (b₁ * c₂ + c₁ * b₂) + (b₁ * c₁ + b₂ * c₂) * a₂)
        _ = a₁ * (b₁ * c₁ + b₂ * c₂) + a₂ * (b₁ * c₂ + c₁ * b₂) + ((a₁ * b₁ + a₂ * b₂) * c₂ + c₁ * (a₁ * b₂ + b₁ * a₂)) := sorry--by simp_semiring
  mul_one := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
      constructor
      · exact h.unit_mem
      · simp_semiring
    )
  distrib :=  by
    constructor <;> (
      intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
      apply Quotient.sound
      exists 0
      constructor
      exact h.unit_mem
      repeat rw [add_zero_right]
    )
    · calc
        a₁ * (b₁ + c₁) + a₂ * (b₂ + c₂) + (a₁ * b₂ + b₁ * a₂ + (a₁ * c₂ + c₁ * a₂))
        _ = a₁ * b₁ + a₂ * b₂ + (a₁ * c₁ + a₂ * c₂) + (a₁ * (b₂ + c₂) + (b₁ + c₁) * a₂) := by simp_semiring
    · calc
        (a₁ + b₁) * c₁ + (a₂ + b₂) * c₂ + (a₁ * c₂ + c₁ * a₂ + (b₁ * c₂ + c₁ * b₂))
        _ = a₁ * c₁ + a₂ * c₂ + (b₁ * c₁ + b₂ * c₂) + ((a₁ + b₁) * c₂ + c₁ * (a₂ + b₂)) := by simp_semiring
}



-- Prove that the localization of a semiring wrt. addition at the full set,
-- i.e. group of differences, is a ring.

-- Define the "negative" operation on α × β.

def quotient.lower.neg_pre: α × (@Set.full α) → α × (@Set.full α) :=
  λ (a₁, a₂) ↦ (a₂, ⟨a₁, trivial⟩)

-- Prove if a ≈ b, then -a ≈ -b.

theorem quotient.lower.neg_lifts : ∀ a b: (α × (@Set.full α)), a ≈ b → Quotient.mk (setoid R.toAddMonoid.full_sub) (quotient.lower.neg_pre a) = Quotient.mk (setoid R.toAddMonoid.full_sub) (quotient.lower.neg_pre b) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · calc
      a₂ + b₁ + t
      _ = b₁ + a₂ + t := by simp [add_comm]
      _ = a₁ + b₂ + t := by rw [ht₂]
      _ = b₂ + a₁ + t := by simp [add_comm]

def quotient.lower.neg: quotient R.toAddMonoid.full_sub → quotient R.toAddMonoid.full_sub :=
  λ x ↦ Quotient.liftOn x _ (quotient.lower.neg_lifts)

instance Localization.additive_group_of_differences [R: Semiring α]: Ring (quotient R.full_ideal.toSubmonoid) := {
  add       := (Localization.additive R.full_ideal).add
  zero      := (Localization.additive R.full_ideal).zero
  add_assoc := (Localization.additive R.full_ideal).add_assoc
  add_zero  := (Localization.additive R.full_ideal).add_zero
  add_comm  := (Localization.additive R.full_ideal).add_comm
  mul       := (Localization.additive R.full_ideal).mul
  one       := (Localization.additive R.full_ideal).one
  mul_assoc := (Localization.additive R.full_ideal).mul_assoc
  mul_one   := (Localization.additive R.full_ideal).mul_one
  distrib   := (Localization.additive R.full_ideal).distrib
  neg       := quotient.lower.neg
  add_neg   := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
      constructor
      · trivial
      · simp [add_zero_right, op_comm]
    )
}

-- TODO: the additive localization of a commutative semiring should give a commutative ring.

end Additive



section Multiplicative

variable {α: Type u} [R: CommRing α] {β: Set α}

-- Multiplicative localization of a commutative ring.

-- Define the lower operation "addition" on α × β.

def quotient.lower.op_pre (h: R.toMulMonoid.sub β): Op (α × β) :=
  λ (a₁, ⟨a₂, h₁⟩) (b₁, ⟨b₂, h₂⟩) ↦ (a₁ * b₂ + b₁ * a₂, ⟨a₂ * b₂, h.op_closed a₂ b₂ h₁ h₂⟩)

-- Prove if a ≈ c and b ≈ d, then a + b ≈ c + d.

theorem quotient.lower.op_lifts (h: R.toMulMonoid.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.lower.op_pre h a b) = Quotient.mk (setoid h) (quotient.lower.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · have ht₁₂: a₁ * c₂ * t₁ = c₁ * a₂ * t₁ := ht₁₂
    have ht₂₂: b₁ * d₂ * t₂ = d₁ * b₂ * t₂ := ht₂₂
    calc
      (((a₁ * b₂ + b₁ * a₂) * (c₂ * d₂))) * (t₁ * t₂)
      _ = (b₁ * d₂ * t₂) * c₂ * a₂ * t₁ + (a₁ * c₂ * t₁) * b₂ * t₂ * d₂ := by simp_semiring
      _ = (d₁ * b₂ * t₂) * c₂ * a₂ * t₁ + (c₁ * a₂ * t₁) * b₂ * t₂ * d₂ := by rw [ht₁₂, ht₂₂]
      _ = ((c₁ * d₂ + d₁ * c₂) * (a₂ * b₂)) * (t₁ * t₂)                 := by simp_semiring



def quotient.lower.op (h: R.toMulMonoid.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.lower.op_lifts h)

-- Define the (additive) inverse operation on α × β.

def quotient.lower.inv_pre: α × β → α × β :=
  λ (a₁, a₂) ↦ (-a₁, a₂)

-- Prove if a ≈ b, then -a ≈ -b.

theorem quotient.lower.inv_lifts (h: R.toMulMonoid.sub β): ∀ a b: (α × β), a ≈ b → Quotient.mk (setoid h) (quotient.lower.inv_pre a) = Quotient.mk (setoid h) (quotient.lower.inv_pre b) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · have ht₂: a₁ * b₂ * t = b₁ * a₂ * t := by exact ht₂
    calc
      (-a₁ * b₂) * t
      _ = -(a₁ * b₂) * t := by rw [mul_neg_left]
      _ = -(a₁ * b₂ * t) := by repeat rw [mul_neg_left]
      _ = -(b₁ * a₂ * t) := by rw [ht₂]
      _ = (-b₁ * a₂) * t := by repeat rw [←mul_neg_left]

def quotient.lower.inv (h: R.toMulMonoid.sub β): quotient h → quotient h :=
  λ x ↦ Quotient.liftOn x _ (quotient.lower.inv_lifts h)

-- Prove that the localization of a commutative ring wrt. multiplication is a
-- commutative ring.

instance Localization.multiplicative [R: CommRing α] (h: R.toMulMonoid.sub β): CommRing (quotient h) := {
  mul       := (Localization h).op
  one       := (Localization h).unit
  mul_assoc := (Localization h).assoc
  mul_one   := (Localization h).identity
  mul_comm  := (Localization h).comm
  add := quotient.lower.op h
  zero := Quotient.mk _ (0, ⟨1, h.unit_mem⟩)
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    apply Quotient.sound
    exists 1
    constructor
    · exact h.unit_mem
    · calc
        ((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) * 1
        _ = (a₁ * (b₂ * c₂) + (b₁ * c₂ + c₁ * b₂) * a₂) * (a₂ * b₂ * c₂) * 1 := by simp_semiring
  add_zero := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      exists 1
      constructor
      exact h.unit_mem
    )
    · calc
      (0 * a₂ + a₁ * 1) * a₂ * 1
      _ = a₁ * (1 * a₂) * 1 := by simp [mul_zero_left, add_zero_left, mul_assoc]
    · calc
      (a₁ * 1 + 0 * a₂) * a₂ * 1
      _ = a₁ * (a₂ * 1) * 1 := by simp [mul_zero_left, add_zero_right, mul_one_right]
  neg := quotient.lower.inv h
  add_neg := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      exists 1
      constructor
      · exact h.unit_mem
    )
    · calc
        (((-a₁ * a₂) + (a₁ * a₂)) * 1) * 1
        _ = (-a₁ * a₂) + (a₁ * a₂) := by simp [mul_one_right]
        _ = -(a₁ * a₂) + (a₁ * a₂) := by rw [mul_neg_left]
        _ = 0                      := by apply op_inv_left
        _ = (0 * (a₂ * a₂)) * 1    := by simp [mul_zero_left]
    · calc
        (((a₁ * a₂) + (-a₁ * a₂)) * 1) * 1
        _ = (a₁ * a₂) + (-a₁ * a₂) := by simp [mul_one_right]
        _ = (a₁ * a₂) + -(a₁ * a₂) := by rw [mul_neg_left]
        _ = 0                      := by apply op_inv_right
        _ = (0 * (a₂ * a₂)) * 1    := by simp [mul_zero_left]
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    apply Quotient.sound
    exists 1
    constructor
    · exact h.unit_mem
    · calc
        ((a₁ * b₂ + b₁ * a₂) * (b₂ * a₂)) * 1
        _ = ((b₁ * a₂ + a₁ * b₂) * (a₂ * b₂)) * 1 := by simp [mul_comm, add_comm]
  distrib := by
    constructor <;> (
      intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
      apply Quotient.sound
      exists 1
      constructor
      · exact h.unit_mem
    )
    · calc
        ((a₁ * ((b₁ * c₂) + (c₁ * b₂))) * ((a₂ * b₂) * (a₂ * c₂))) * 1
        _ = ((((a₁ * b₁) * (a₂ * c₂)) + ((a₁ * c₁) * (a₂ * b₂))) * (a₂ * (b₂ * c₂))) * 1 := by simp_semiring
    · calc
        ((((a₁ * b₂) + (b₁ * a₂)) * c₁) * ((a₂ * c₂) * (b₂ * c₂))) * 1
        _ = (((a₁ * c₁) * (b₂ * c₂) + (b₁ * c₁) * (a₂ * c₂)) * ((a₂ * b₂) * c₂)) * 1 := by simp_semiring
}

-- Prove that if α is an integral domain, then the localization wrt.
-- multiplication at α \ {0} is a field (field of fractions).

def setoid.nonzero [I: IntegralDomain α]: Setoid (α × I.nonzero) :=
  @setoid _ I.toMulMonoid _ I.nonzero_submonoid

abbrev quotient.nonzero (α: Type u) [I: IntegralDomain α]: Type u :=
  @quotient _ I.toMulMonoid _ I.nonzero_submonoid

-- Define the multiplicative inverse operation on α \ {0} × α \ {0}.
-- 0 = [(0, 1)] does not get an inverse.

def quotient.upper.inv_pre [I: IntegralDomain α]: (I.nonzero × I.nonzero) → (I.nonzero × I.nonzero) :=
  λ (a₁, a₂) ↦ (a₂, a₁)

-- TODO Prove if a ≈ b, then a⁻¹ ≈ b⁻¹

instance Localization.field_of_fractions [I: IntegralDomain α]: Field (quotient.nonzero α) := {
  inv := sorry
  mul_inverses := sorry
}

end Multiplicative

section OrderLift

open Monoid

variable {α: Type u} [P: PartialOrder α] [M: CommMonoid α] {β: Set α}

-- Lifting the order structure to the localization
-- (a, b) ≤ (c, d)

def order_compatible (M: CommMonoid α) (P: PartialOrder α): Prop :=
  ∀ {a b c: α}, a ≤ b → a + c ≤ b + c

def quotient.le_pre: Endorelation (α × β) :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ t, a₁ + b₂ + t ≤ b₁ + a₂ + t

instance: Trans P.le P.le P.le := {
  trans := @P.transitive
}

-- Need the monoid M to have the property
-- a ≤ b ↔ a + c ≤ b + c

theorem quotient.le_lifts_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b → quotient.le_pre c d := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩ ⟨t, ht⟩
  let t' := b₁ + t₂ + a₂ + t₁ + t
  exists t'
  calc
    c₁ + d₂ + (b₁ + t₂ + a₂ + t₁ + t)
    _ = (c₁ + a₂ + t₁) + (b₁ + d₂ + t₂) + t := by simp_monoid
    _ = (a₁ + c₂ + t₁) + (d₁ + b₂ + t₂) + t := by rw [ht₁₂, ht₂₂]
    _ = (a₁ + b₂ + t) + (c₂ + d₁ + t₁ + t₂) := by simp_monoid
    _ ≤ (b₁ + a₂ + t) + (c₂ + d₁ + t₁ + t₂) := by apply h ht
    _ = d₁ + c₂ + (b₁ + t₂ + a₂ + t₁ + t)   := by simp_monoid

theorem quotient.le_lifts (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b = quotient.le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  exact le_lifts_imp h a b c d h₁ h₂
  exact le_lifts_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_lifts h₀ h)

section MultiplicativeOrderLift

section OrderLift

open Monoid

def quotient.mul_le_pre: Endorelation (α × β) :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ t, a₁ + a₂ + b₂ + b₂ + t ≤ b₁ + a₂ + a₂ + b₂ + t

theorem quotient.mul_le_lifts_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b → quotient.mul_le_pre c d := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩ ⟨t, ht⟩
  let t': α := a₂ + a₂ + b₁ + b₂ + t₁ + t₂ + t
  exists t'
  calc
    c₁ + c₂ + d₂ + d₂ + (a₂ + a₂ + b₁ + b₂ + t₁ + t₂ + t)
    _ = (c₁ + a₂ + t₁) + (b₁ + d₂ + t₂) + (a₂ + b₂ + c₂ + d₂ + t) := by simp_monoid
    _ = (a₁ + c₂ + t₁) + (d₁ + b₂ + t₂) + (a₂ + b₂ + c₂ + d₂ + t) := by rw [ht₁₂, ht₂₂]
    _ = (a₁ + a₂ + b₂ + b₂ + t) + (c₂ + c₂ + d₁ + d₂ + t₁ + t₂)   := by simp_monoid
    _ ≤ (b₁ + a₂ + a₂ + b₂ + t) + (c₂ + c₂ + d₁ + d₂ + t₁ + t₂)   := by apply h ht
    _ = d₁ + c₂ + c₂ + d₂ + (a₂ + a₂ + b₁ + b₂ + t₁ + t₂ + t)     := by simp_monoid

theorem quotient.mul_le_lifts (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b = quotient.mul_le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  · exact mul_le_lifts_imp h a b c d h₁ h₂
  · exact mul_le_lifts_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.mul_le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_lifts h₀ h)
