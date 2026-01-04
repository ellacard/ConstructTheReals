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
