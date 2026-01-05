import ConstructTheReals.FieldOfFractions
import ConstructTheReals.Integer
import ConstructTheReals.MetricSpace

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

namespace ℚ

instance Field: Field ℚ :=
  ℤ.IntegralDomain.field_of_fractions

-- TODO add to Field file
instance: Div ℚ := ⟨sorry⟩

instance Lattice: Lattice ℚ :=
  sorry



-- More theorems

theorem le_add_left {a b c: ℚ} (h: b ≤ c): a + b ≤ a + c := by
  sorry

theorem le_add_right {a b c: ℚ} (h: a ≤ b): a + c ≤ b + c := by
  sorry

theorem le_add_left' (a: ℚ) {b c: ℚ} (h: a + b ≤ a + c): b ≤ c := by
  sorry

theorem le_add_right' {a b: ℚ} (c: ℚ) (h: a + c ≤ b + c): a ≤ b := by
  sorry

theorem div_nonnegative_nonnegative {a b: ℚ} (ha: 0 ≤ a) (hb: 0 ≤ b) (hb₀: b ≠ 0): 0 ≤ a / b := by
  sorry

theorem div_nonzero {a b: ℚ} (ha: a ≠ 0) (hb: b ≠ 0): a / b ≠ 0 := by
  sorry



-- Define absolute value.

instance: ∀ a b: ℚ, Decidable (a ≤ b) := sorry

def abs (a: ℚ): ℚ :=
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



-- Embedding of ℤ in ℚ.

instance: Coe ℤ ℚ := ⟨λ n ↦ Quotient.mk _ (n, ⟨1, ℤ.one_nonzero⟩)⟩
instance (n: Nat): OfNat ℚ n := ⟨ℕ.fromNat n⟩
