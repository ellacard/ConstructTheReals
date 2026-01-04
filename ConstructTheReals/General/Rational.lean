import ConstructTheReals.General.FieldOfFractions
import ConstructTheReals.General.Integer
import ConstructTheReals.General.MetricSpace

/-

Define the rationals as the field of fractions of the integers.

Properties of ℚ:
- (ℚ, +, *) is a field
- (ℚ, ≤) is a lattice
- Other order properties?

-/

def Rational: Type :=
  ℤ.IntegralDomain.field_of_fractions_type

abbrev ℚ: Type :=
  Rational

instance ℚ.Field: Field ℚ :=
  ℤ.IntegralDomain.field_of_fractions

instance ℚ.Lattice: Lattice ℚ :=
  sorry



-- Define the nonnegative rationals.

def NNRational: Type :=
  Subtype (λ x: ℚ ↦ 0 ≤ x)

abbrev NNℚ: Type :=
  NNRational



-- Define absolute value.

instance: ∀ a b: ℚ, Decidable (a ≤ b) := sorry

def ℚ.abs (a: ℚ): ℚ :=
  if 0 ≤ a then a else -a

theorem abs_eq (a: ℚ): ℚ.abs a = if 0 ≤ a then a else -a := by
  rfl

theorem zero_le_abs (a: ℚ): 0 ≤ ℚ.abs a := by
  simp [ℚ.abs]
  by_cases h: 0 ≤ a
  · rw [if_pos h]
    exact h
  · rw [if_neg h]
    sorry

def NNℚ.abs (a: ℚ): NNℚ :=
  ⟨ℚ.abs a, zero_le_abs a⟩

theorem abs_eq' (a: ℚ): NNℚ.abs a = ⟨if 0 ≤ a then a else -a, zero_le_abs a⟩ := by
  rfl



-- Embedding of ℤ in ℚ.

instance: Coe ℤ ℚ := ⟨λ n ↦ Quotient.mk _ (n, ⟨1, ℤ.one_nonzero⟩)⟩
