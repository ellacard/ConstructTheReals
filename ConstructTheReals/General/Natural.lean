import ConstructTheReals.Natural
import ConstructTheReals.General.Order
import ConstructTheReals.General.Ring

/-

Define the semiring and lattice on ℕ.

-/

open ℕ

instance NaturalSemiring: CommSemiring ℕ := {
  add := add
  zero := zero
  add_assoc := add_assoc
  add_zero := ⟨add_zero_left, add_zero_right⟩
  add_comm := add_comm
  mul := mul
  one := one
  mul_assoc := mul_assoc
  mul_one := ⟨mul_one_left, mul_one_right⟩
  distrib := ⟨distrib_left, distrib_right⟩
  mul_comm := mul_comm
}

instance NaturalLattice: Lattice ℕ := {
  reflexive := le_refl
  transitive := @le_trans
  antisymmetric := @le_antisymm
  min := min
  max := max
  max_le_left := max_le_left
  max_le_right := max_le_right
  max_lub := sorry
  min_le_left := sorry
  min_le_right := sorry
  min_glb := sorry
}
