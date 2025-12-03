import ConstructTheReals.Simple.Integer

def Set (α: Type u): Type u :=
  α → Prop

instance (α: Type u): CoeSort (Set α) (Type u) := {
  coe := Subtype
}

def ℤ.nonzero: Set ℤ :=
  λ a ↦ a ≠ 0

def ℚ: Type := @Quotient (ℤ × ℤ.nonzero) {
  r := λ (a₁, a₂) (b₁, b₂) ↦ a₁ * b₂ = b₁ * a₂
  iseqv := {
    refl := by intro; rfl
    symm := Eq.symm
    trans := by
      intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
      simp
      intro h₁ h₂
      sorry
  }
}

instance: Zero ℚ :=
  sorry

instance: LE ℚ :=
  sorry

#check Inv
