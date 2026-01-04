import ConstructTheReals.General.MetricSpace
import ConstructTheReals.General.Rational

/-

Define the real numbers as the completion of the (general) metric space on the rationals.

Properties of ℝ:
- ...

-/



-- First, define the nonnegative rationals ℚ₊.

def NNRational: Type :=
  Subtype (λ x: ℚ ↦ 0 ≤ x)

abbrev nnℚ: Type :=
  NNRational

-- Show ℚ₊ satisfies the necessary properties for a generalized metric space.

instance: DistanceSpace nnℚ := {
  le := sorry
  le_refl := sorry
  le_trans := sorry
  le_antisymm := sorry
  bottom := sorry
  bottom_le := sorry
  add := sorry
  add_assoc := sorry
  add_bottom := sorry
  le_add := sorry
}



-- Next, define a metric ℚ × ℚ → ℚ₊.

instance ℚ.metric: Metric ℚ nnℚ := {
  distance := sorry
  distance_bot_iff := sorry
  distance_symm := sorry
  distance_triangle := sorry
}

instance nnℚ.endometric: Endometric nnℚ := {
  distance := sorry
  distance_bot_iff := sorry
  distance_symm := sorry
  distance_triangle := sorry
}

-- Show the metrics satisfy the necessary properties for the Cauchy sequence equivalence.

theorem nnℚ.endometric_obedient: nnℚ.endometric.obedient := by
  sorry

theorem nnℚ.distance_complete: DistanceComplete nnℚ := by
  sorry



-- Finally, define the real numbers as the quotient on cauchy sequences of rationals using the above metrics on ℚ.

def Real: Type :=
  CauchyRelation.quotient
    nnℚ.distance_complete
    nnℚ.endometric
    nnℚ.endometric_obedient
    ℚ.metric

abbrev ℝ: Type :=
  Real



-- ℝ is a field.
-- TODO this will take a lot of work..

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
-- TODO this too..

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
