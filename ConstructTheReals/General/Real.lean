import ConstructTheReals.General.MetricSpace
import ConstructTheReals.General.Rational

/-

Define the real numbers as the completion of the (general) metric space on the rationals.

Properties of ℝ:
- ...

-/

def Real: Type :=
  CauchyRelation.quotient
    NNRational.distance_complete
    NNRational.endometric
    NNRational.endometric_obedient
    Rational.metric

abbrev ℝ: Type :=
  Real

-- ℝ is a field.

instance ℝ.Field: Field ℝ := {
  add := sorry
  zero := sorry
  add_assoc := sorry
  add_zero := sorry
  add_comm := sorry
  mul := sorry
  one := sorry
  mul_assoc := sorry
  mul_one := sorry
  distrib := sorry
  neg := sorry
  add_neg := sorry
  mul_comm := sorry
  inv := sorry
  mul_inverses := sorry
}

-- ℝ is a lattice.

instance ℝ.Lattice: Lattice ℝ := {
  le := sorry
  reflexive := sorry
  transitive := sorry
  antisymmetric := sorry
  min := sorry
  max := sorry
  max_le_left := sorry
  max_le_right := sorry
  max_lub := sorry
  min_le_left := sorry
  min_le_right := sorry
  min_glb := sorry
}

-- TODO More properties of ℝ
