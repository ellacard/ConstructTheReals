import ConstructTheReals.SetTheory.Function
import ConstructTheReals.SetTheory.Subset

def Finite (α: Type u): Prop :=
  ∃ n, Nonempty (Invertible α (Fin n))

def Set.finite {α: Type u} (S: Set α): Prop :=
  Finite S
