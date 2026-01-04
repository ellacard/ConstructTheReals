import ConstructTheReals.General.GroupOfDifferences
import ConstructTheReals.General.Natural

/-

Define the integers as the group of differences of the natural numbers.

Properties of ℤ:
- (ℤ, +, *) is an integral domain (a nonzero commutative ring with no zero divisors)
- (ℤ, ≤) is a lattice
- Other order properties?

-/

def Integer: Type :=
  ℕ.CommSemiring.group_of_differences_type

abbrev ℤ: Type :=
  Integer

instance ℤ.CommRing: CommRing ℤ :=
  ℕ.CommSemiring.group_of_differences

instance ℤ.IntegralDomain: IntegralDomain ℤ := {
  no_zero_divisors := sorry
  nontrivial := sorry
}

instance ℤ.Lattice: Lattice ℤ :=
 sorry



 -- Other integer theorems.

 theorem ℤ.one_nonzero: (1: ℤ) ≠ 0 := by
  sorry



-- Embedding of ℕ in ℤ.

instance: Coe ℕ ℤ := ⟨λ n ↦ Quotient.mk _ (n, ⟨0, trivial⟩)⟩
