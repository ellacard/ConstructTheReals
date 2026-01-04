import ConstructTheReals.General.Field
import ConstructTheReals.General.Localization

/-

Part 1: Localization of a commutative ring's 'multiplicative monoid'

    (CommRing -> CommRing)

-/

namespace MultiplicativeLocalization

section Multiplicative
open Localization
variable {α: Type u} [R: CommRing α] {β: Set α}

-- Given a commutative ring on α, define addition on α × β.

def add_pre (h: R.toMulMonoid.sub β): Op (α × β) :=
  λ (a₁, ⟨a₂, h₁⟩) (b₁, ⟨b₂, h₂⟩) ↦ (a₁ * b₂ + b₁ * a₂, ⟨a₂ * b₂, h.op_closed a₂ b₂ h₁ h₂⟩)

-- Prove if a ≈ c and b ≈ d, then a + b ≈ c + d.

theorem add_well_defined (h: R.toMulMonoid.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (add_pre h a b) = Quotient.mk (setoid h) (add_pre h c d) := by
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

def add (h: R.toMulMonoid.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (add_well_defined h)

-- Define the (additive) inverse operation on α × β.

def add_inv_pre: α × β → α × β :=
  λ (a₁, a₂) ↦ (-a₁, a₂)

-- Prove if a ≈ b, then -a ≈ -b.

theorem add_inv_well_defined (h: R.toMulMonoid.sub β): ∀ a b: (α × β), a ≈ b → Quotient.mk (setoid h) (add_inv_pre a) = Quotient.mk (setoid h) (add_inv_pre b) := by
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

def add_inv (h: R.toMulMonoid.sub β): quotient h → quotient h :=
  λ x ↦ Quotient.liftOn x _ (add_inv_well_defined h)

-- Prove that the localization of a commutative ring wrt. multiplication is a
-- commutative ring.

def multiplicative_localization (h: R.toMulMonoid.sub β): CommRing (Localization.quotient h) := {
  mul       := (localization h).op
  one       := (localization h).unit
  mul_assoc := (localization h).assoc
  mul_one   := (localization h).identity
  mul_comm  := (localization h).comm
  add := add h
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
  neg := add_inv h
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

end Multiplicative

end MultiplicativeLocalization

instance CommRing.multiplicative_localization {α: Type u} [R: CommRing α] {β: Set α} (h: R.toMulMonoid.sub β): CommRing (Localization.quotient h) :=
  MultiplicativeLocalization.multiplicative_localization h



/-

Part 2: Field of fractions

    (IntegralDomain -> Field)

-/

namespace FieldOfFractions

section Basic
open Classical
variable {α: Type u} [I: IntegralDomain α]

abbrev setoid: Setoid (α × I.nonzero) :=
  @Localization.setoid _ I.toMulMonoid _ I.nonzero_submonoid

abbrev quotient [I: IntegralDomain α]: Type u :=
  @Localization.quotient _ I.toMulMonoid _ I.nonzero_submonoid

instance: HasEquiv (α × I.nonzero) := ⟨setoid.r⟩

-- TODO define multiplicative inverses

def field_of_fractions: Field (@quotient α I) := {
  inv := sorry
  mul_inverses := sorry
}

end Basic
end FieldOfFractions

def IntegralDomain.field_of_fractions_type {α: Type u} [I: IntegralDomain α]: Type u :=
  @FieldOfFractions.quotient α I

instance IntegralDomain.field_of_fractions {α: Type u} [I: IntegralDomain α]: Field (@FieldOfFractions.quotient α I) :=
  FieldOfFractions.field_of_fractions
