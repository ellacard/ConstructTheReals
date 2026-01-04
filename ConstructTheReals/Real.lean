import ConstructTheReals.MetricSpace
import ConstructTheReals.Rational

/-

Define the real numbers as the completion of the (general) metric space on the rationals.

Properties of ℝ:
- ...

-/

-- First, show ℚ₊ satisfies the necessary properties for a generalized metric space.

instance: Coe NNℚ ℚ := ⟨λ ⟨q, _⟩ ↦ q⟩

instance: DistanceSpace NNℚ := {
  le          := λ a b ↦ ℚ.Lattice.le a b
  le_refl     := λ a ↦ ℚ.Lattice.reflexive a
  le_trans    := λ a b c ↦ ℚ.Lattice.transitive a b c
  le_antisymm := λ a b h₁ h₂ ↦ Subtype.ext (ℚ.Lattice.antisymmetric a b h₁ h₂)
  bottom := ⟨0, ℚ.Lattice.reflexive 0⟩
  bottom_le := λ ⟨_, ha⟩ ↦ ha
  add := λ ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a + b, sorry⟩
  add_assoc := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp
    sorry
  add_bottom := by
    constructor
    · intro ⟨_, _⟩
      simp [add_zero_left]
    · intro ⟨_, _⟩
      simp [add_zero_right]
  le_add := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp
    constructor
    · intro h
      sorry
    · intro h
      sorry
}



-- Next, define a metric ℚ × ℚ → ℚ₊.

instance ℚ.metric: Metric ℚ NNℚ := {
  distance := λ a b ↦ NNℚ.abs (a - b)
  distance_bot_iff := by
    intro a b
    constructor
    · intro h
      sorry
    · intro h
      sorry
  distance_symm := by
    intro a b
    sorry
  distance_triangle := by
    intro a b c
    sorry
}

instance NNℚ.endometric: Endometric NNℚ := {
  distance := λ a b ↦ ℚ.metric.distance a b
  distance_bot_iff := sorry
  distance_symm := λ a b ↦ ℚ.metric.distance_symm a b
  distance_triangle := λ a b c ↦ ℚ.metric.distance_triangle a b c
}

theorem dist_eq {a b: NNℚ}: NNℚ.endometric.distance a b = NNℚ.abs (a - b) := by
  rfl

-- Show the metrics satisfy the necessary properties for the Cauchy sequence equivalence.

theorem NNℚ.endometric_obedient: NNℚ.endometric.obedient := by
  intro ⟨r, hr⟩
  simp [dist_eq]
  simp [sub_zero_right]
  by_cases h: 0 ≤ r
  · simp [abs_eq', if_pos h]
  · contradiction

-- This is unnecessarily complicated? maybe we should do a less general metric?
instance: Div NNℚ := ⟨sorry⟩
instance: Coe ℕ NNℚ := ⟨sorry⟩

theorem NNℚ.distance_complete: DistanceComplete NNℚ := by
  intro a ha
  --exists a / 2
  sorry



-- Finally, define the real numbers as the quotient on cauchy sequences of rationals using the above metrics on ℚ.

def Real: Type :=
  CauchyRelation.quotient
    NNℚ.distance_complete
    NNℚ.endometric
    NNℚ.endometric_obedient
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
