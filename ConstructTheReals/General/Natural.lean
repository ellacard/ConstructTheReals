import ConstructTheReals.Natural
import ConstructTheReals.General.Relation
import ConstructTheReals.General.Ring

/-

Properties of ℕ:
- (ℕ, +, *) is a commutative semiring
- (ℕ, ≤) is a lattice

-/

open ℕ

instance ℕ.CommSemiring: CommSemiring ℕ := {
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

instance ℕ.Lattice: Lattice ℕ := {
  reflexive := le_refl
  transitive := @le_trans
  antisymmetric := @le_antisymm
  min := ℕ.min
  max := ℕ.max
  max_le_left := max_le_left
  max_le_right := max_le_right
  max_lub := sorry
  min_le_left := sorry
  min_le_right := sorry
  min_glb := sorry
}

/-

TODO
Subtraction of natural numbers, truncated at 0. If a result would be less than zero, then the result is zero.

-/

instance: Sub ℕ := {
  sub := sorry
}

-- TODO Additional natural number theorems.

theorem ℕ.le_add_of_sub_le {a b c : ℕ} (h : a - b ≤ c) : a ≤ c + b := by
  sorry

theorem ℕ.le_of_add_left_le {n m k : ℕ} (h : k + n ≤ m) : n ≤ m := by
  sorry

theorem ℕ.le_sub_of_add_le {a b c : ℕ} (h : a + b ≤ c) : a ≤ c - b := by
  sorry

theorem ℕ.sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n := by
  sorry

theorem ℕ.le_of_not_ge {a b : ℕ} : ¬a ≥ b → a ≤ b := by
  sorry
