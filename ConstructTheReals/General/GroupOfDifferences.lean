import ConstructTheReals.General.Group
import ConstructTheReals.General.Ring
import ConstructTheReals.General.Localization

/-

Part 1: Group of differences

    (CommMonoid -> CommGroup)

-/

namespace GroupOfDifferences

section Basic
open Monoid

variable {α: Type u} [M: CommMonoid α]

abbrev setoid: Setoid (α × Set.full α) :=
  Localization.setoid M.full_sub

abbrev quotient (α: Type u) [M: CommMonoid α]: Type u :=
  Localization.quotient M.full_sub

-- Given a commutative monoid on α, define the additive inverse operation on α × α.

def inverse_pre: α × Set.full α → α ×  Set.full α :=
  λ (a₁, a₂) ↦ (a₂, ⟨a₁, trivial⟩)

theorem inverse_well_defined: ∀ a b: α × Set.full α, a ≈ b → Quotient.mk setoid (inverse_pre a) = Quotient.mk setoid (inverse_pre b) := by
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

def inverse: quotient α → quotient α :=
  λ x ↦ Quotient.liftOn x _ inverse_well_defined

-- Show α / α is a commutative group (the group of differences).

def group_of_differences: CommGroup (quotient α) := {
  inv := inverse
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

end Basic
end GroupOfDifferences

def CommMonoid.group_of_differences {α: Type u} [M: CommMonoid α]: CommGroup (GroupOfDifferences.quotient α) :=
  GroupOfDifferences.group_of_differences



/-

Part 2: Group of differences of a commutative semiring's 'additive monoid'

    (CommSemiRing -> CommRing)

-/

namespace AdditiveGroupOfDifferences
section Additive
open Ring

variable {α: Type u} [R: CommSemiring α]
instance: HasEquiv (α × Set.full α) := ⟨(@GroupOfDifferences.setoid α R.toAddMonoid).r⟩

-- Given a commutative semiring on α, define multiplication on α × α.

def mul_pre: Op (α × Set.full α) :=
  λ (a₁, ⟨a₂, _⟩) (b₁, ⟨b₂, _⟩) ↦ (a₁ * b₁ + a₂ * b₂, ⟨a₁ * b₂ + b₁ * a₂, trivial⟩)

-- Prove if a ≈ c and b ≈ d, then a * b ≈ c * d.

theorem mul_well_defined: ∀ a b c d: (α × Set.full α), a ≈ c → b ≈ d → Quotient.mk (@GroupOfDifferences.setoid α R.toAddMonoid) (mul_pre a b) = Quotient.mk (@GroupOfDifferences.setoid α R.toAddMonoid) (mul_pre c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  have t: α := sorry
  exists t
  constructor
  · trivial
  · sorry

def mul: Op (@GroupOfDifferences.quotient α R.toAddMonoid) :=
  λ x y ↦ Quotient.liftOn₂ x y _ mul_well_defined

-- Prove that the group of differences of a commutative semiring's 'additive monoid' is a commutative ring.

instance additive_god: CommGroup (@GroupOfDifferences.quotient α R.toAddMonoid) := R.toAddMonoid.group_of_differences

instance group_of_differences: CommRing (@GroupOfDifferences.quotient _ R.toAddMonoid) := {
  add       := additive_god.op
  zero      := additive_god.unit
  add_assoc := additive_god.assoc
  add_zero  := additive_god.identity
  add_comm  := additive_god.comm
  neg       := additive_god.inv
  add_neg   := additive_god.inverse
  mul       := mul
  one       := Quotient.mk _ (1, ⟨0, trivial⟩)
  mul_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    apply Quotient.sound
    exists 0
    constructor
    · trivial
    · repeat rw [add_zero_right]
      calc
        (a₁ * b₁ + a₂ * b₂) * c₁ + (a₁ * b₂ + b₁ * a₂) * c₂ + (a₁ * (b₁ * c₂ + c₁ * b₂) + (b₁ * c₁ + b₂ * c₂) * a₂)
        _ = a₁ * (b₁ * c₁ + b₂ * c₂) + a₂ * (b₁ * c₂ + c₁ * b₂) + ((a₁ * b₁ + a₂ * b₂) * c₂ + c₁ * (a₁ * b₂ + b₁ * a₂)) := sorry --by simp_semiring
  mul_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩
    apply Quotient.sound
    exists 0
    constructor
    · trivial
    · repeat rw [add_zero_right]
      calc
        a₁ * b₁ + a₂ * b₂ + (b₁ * a₂ + a₁ * b₂)
        _ = a₁ * b₁ + a₂ * b₂ + (a₁ * b₂ + b₁ * a₂) := by rw [add_comm (b₁ * a₂) (a₁ * b₂)]
        _ = b₁ * a₁ + b₂ * a₂ + (a₁ * b₂ + b₁ * a₂) := by
          have h1: a₁ * b₁ = b₁ * a₁ := mul_comm a₁ b₁
          have h2: a₂ * b₂ = b₂ * a₂ := mul_comm a₂ b₂
          rw [h1, h2]
  mul_one := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
      constructor
      · trivial
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
      trivial
      repeat rw [add_zero_right]
    )
    · calc
        a₁ * (b₁ + c₁) + a₂ * (b₂ + c₂) + (a₁ * b₂ + b₁ * a₂ + (a₁ * c₂ + c₁ * a₂))
        _ = a₁ * b₁ + a₂ * b₂ + (a₁ * c₁ + a₂ * c₂) + (a₁ * (b₂ + c₂) + (b₁ + c₁) * a₂) := by simp_semiring
    · calc
        (a₁ + b₁) * c₁ + (a₂ + b₂) * c₂ + (a₁ * c₂ + c₁ * a₂ + (b₁ * c₂ + c₁ * b₂))
        _ = a₁ * c₁ + a₂ * c₂ + (b₁ * c₁ + b₂ * c₂) + ((a₁ + b₁) * c₂ + c₁ * (a₂ + b₂)) := by simp_semiring
}

end Additive
end AdditiveGroupOfDifferences

def CommSemiring.group_of_differences_type {α: Type u} [R: CommSemiring α]: Type u :=
  @GroupOfDifferences.quotient _ R.toAddMonoid

instance CommSemiring.group_of_differences {α: Type u} [R: CommSemiring α]: CommRing (@GroupOfDifferences.quotient _ R.toAddMonoid) :=
  AdditiveGroupOfDifferences.group_of_differences
