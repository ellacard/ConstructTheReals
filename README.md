
A construction of the real numbers in Lean 4.

- First natural numbers are constructed by hand as an inductive type (Peano's axioms).
- Then integers are the additive localization (group of differences/Grothendieck group).
- Next the rationals are multiplicative localization of nonzero elements (the field of fractions).
- Finally the reals are the metric space completion via equivalence classes of Cauchy sequences.

The result is a complete ordered field.