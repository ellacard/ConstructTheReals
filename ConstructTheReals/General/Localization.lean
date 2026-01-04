import ConstructTheReals.General.Monoid

namespace Localization
open Monoid

variable {α: Type u} [M: CommMonoid α] {β: Set α}

/-

General localization of a commutative monoid

    (CommMonoid -> CommMonoid)

-/

-- Define the localization relation on α × β.

def relation (β: Set α): α × β → α × β → Prop :=
  λ (a₁, ⟨a₂, _⟩) (b₁, ⟨b₂, _⟩) ↦ ∃ t ∈ β, a₁ + b₂ + t = b₁ + a₂ + t

instance: HasEquiv (α × β) := ⟨relation β⟩

theorem equiv_iff (a₁ b₁: α) (a₂ b₂: β): (a₁, a₂) ≈ (b₁, b₂) ↔ ∃ t ∈ β, a₁ + b₂ + t = b₁ + a₂ + t := by
  rfl

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

theorem quotient.op_well_defined (h: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.op_pre h a b) = Quotient.mk (setoid h) (quotient.op_pre h c d) := by
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
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.op_well_defined h)

-- Show α / β is a commutative monoid.

instance localization (h: M.sub β): CommMonoid (quotient h) := {
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


/-

Old code for lifting order.

Need to consider the best way to do this.




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

theorem quotient.le_well_defined_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b → quotient.le_pre c d := by
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

theorem quotient.le_well_defined (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b = quotient.le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  exact le_well_defined_imp h a b c d h₁ h₂
  exact le_well_defined_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_well_defined h₀ h)

section MultiplicativeOrderLift

section OrderLift

open Monoid

def quotient.mul_le_pre: Endorelation (α × β) :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ t, a₁ + a₂ + b₂ + b₂ + t ≤ b₁ + a₂ + a₂ + b₂ + t

theorem quotient.mul_le_well_defined_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b → quotient.mul_le_pre c d := by
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

theorem quotient.mul_le_well_defined (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b = quotient.mul_le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  · exact mul_le_well_defined_imp h a b c d h₁ h₂
  · exact mul_le_well_defined_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.mul_le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_well_defined h₀ h)


-/
