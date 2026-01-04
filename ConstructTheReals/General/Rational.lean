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



-- Define a metric on Q.

def NNRational: Type :=
  Subtype (λ x: ℚ ↦ 0 ≤ x)

instance: DistanceSpace NNRational :=
  sorry

instance Rational.metric: Metric ℚ NNRational :=
  sorry

-- Also need the endometric on rationals
instance NNRational.endometric: Endometric NNRational :=
  sorry

theorem NNRational.endometric_obedient: NNRational.endometric.obedient := by
  sorry

theorem NNRational.distance_complete: DistanceComplete NNRational := by
  sorry
