import ConstructTheReals.MetricSpace
import ConstructTheReals.Rational

/-

Define the real numbers as the completion of the (general) metric space on the rationals.

Properties of ℝ:
- ...

-/

-- Define a generalized metric space on ℚ.

instance: DistanceSpace ℚ := {
  le          := ℚ.Lattice.le
  le_refl     := ℚ.Lattice.reflexive
  le_trans    := ℚ.Lattice.transitive
  le_antisymm := ℚ.Lattice.antisymmetric
  zero := 0
  add := ℚ.Field.add
  add_assoc := ℚ.Field.add_assoc
  add_zero := ℚ.Field.add_zero
  le_add := by
    intro a b c
    constructor
    · intro h
      apply ℚ.le_add_right
      exact h
    · intro h
      apply ℚ.le_add_right' c
      exact h
  complete := by
    intro a ⟨h₁, h₂⟩
    exists a / 2
    have two_neq_zero: (2: ℚ) ≠ 0 := by sorry
    constructor
    · constructor
      · have temp₂: (0: ℚ) ≤ 2 := by sorry
        exact ℚ.div_nonnegative_nonnegative h₁ temp₂ two_neq_zero
      · exact Ne.symm (ℚ.div_nonzero (Ne.symm h₂) two_neq_zero)
    · sorry
}

instance ℚ.metric: Metric ℚ ℚ := {
  distance := λ a b ↦ ℚ.abs (a - b)
  distance_le := λ a b ↦ zero_le_abs (a - b)
  distance_zero_iff := sorry
  distance_symm := sorry
  distance_triangle := sorry
}

theorem dist_eq {a b: ℚ}: ℚ.metric.distance a b = ℚ.abs (a - b) := by
  rfl

-- Define the real numbers as the quotient on cauchy sequences of rationals using the above metrics on ℚ.

def Real: Type :=
  CauchyRelation.quotient ℚ.metric

abbrev ℝ: Type :=
  Real



-- ℝ is a field.
-- TODO this will take a lot of work..

def add_cauchy (a b: CauchySet ℚ.metric): CauchySet ℚ.metric := by
  sorry

def add (a b: ℝ): ℝ :=
  Quotient.liftOn₂ a b (λ a b ↦ Quotient.mk _ (add_cauchy a b))
  ( by
    sorry
  )

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



-- Embedding of ℚ in ℝ.

instance: Coe ℚ ℝ := ⟨λ n ↦ Quotient.mk _ ⟨ConstantSequence n, constant_sequence_cauchy⟩⟩
instance (n: Nat): OfNat ℝ n := ⟨(ℕ.fromNat n)⟩
