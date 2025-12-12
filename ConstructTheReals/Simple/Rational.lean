import ConstructTheReals.Simple.Integer

/-

Define the rationals ℚ as the quotient on ℤ ⨯ ℤ \ {0} by the relation
  (a₁, a₂) ~ (b₁, b₂) ↔ a₁ * b₂ = b₁ * a₂
thus adjoining multiplicative inverses for every nonzero element of ℤ.

Then, lift the operations + and * and the order ≤ to ℚ.

Properties of ℚ:
- (ℚ, +) is a cancellative commutative group
- (ℚ, *) is a commutative monoid
- (ℚ, +, *) is a field
- (ℚ, ≤) is a lattice

-/

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

theorem ℕ.one_nonzero: (1: ℕ) ≠ 0 := by
  sorry

theorem ℤ.one_nonzero: (1: ℤ) ≠ 0 := by
  sorry

instance: One ℤ.nonzero := ⟨1, ℤ.one_nonzero⟩

namespace ℚ

def zero: ℚ :=
  Quotient.mk _ (0, 1)

instance: Zero ℚ := ⟨zero⟩

def one: ℚ :=
  Quotient.mk _ (1, 1)

instance: One ℚ := ⟨one⟩

-- a/b + c/d = (ad + bc)/(bd)
def add (a b: ℚ): ℚ :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ Quotient.mk _ (a₁*b₂ + b₁*a₂, ⟨a₂*b₂, sorry⟩)) -- this sorry says that ℤ is integral domain, x ≠ 0 ∧ y ≠ 0 → x*y ≠ 0
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    calc
      (a₁ * b₂ + b₁ * a₂) * (c₂ * d₂)
      _ = (c₁ * d₂ + d₁ * c₂) * (a₂ * b₂) := by sorry
  )

instance: Add ℚ := ⟨add⟩

-- -(a/b) = (-a)/b
def neg (a: ℚ): ℚ :=
  Quotient.liftOn a (λ (a₁, a₂) ↦ Quotient.mk _ (-a₁, a₂))
  ( by
    intro (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) h
    apply Quotient.sound
    calc
      (-a₁) * b₂
      _ = (-b₁) * a₂ := by sorry
  )

instance: Neg ℚ := ⟨neg⟩

def mul (a b: ℚ): ℚ :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ Quotient.mk _ (a₁ * b₁, ⟨a₂ * b₂, sorry⟩))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    calc
      (a₁ * b₁) * (c₂ * d₂)
      _ = (c₁ * d₁) * (a₂ * b₂) := sorry
  )

instance: Mul ℚ := ⟨mul⟩

def inv {a: ℚ} (ha: a ≠ 0): ℚ :=
  Quotient.liftOn a (λ (a₁, ⟨a₂, ha₂⟩) ↦ Quotient.mk _ (a₂, ⟨a₁, sorry⟩))
  ( by
    intro (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) h
    apply Quotient.sound
    calc
      a₂ * b₁
      _ = b₂ * a₁ := by sorry
  )

theorem inv_nonzero {a: ℚ} (ha: a ≠ 0): (inv ha) ≠ 0 := by
  sorry

def Nonzero (X: Type u) [Zero X]: Set X :=
  λ x ↦ x ≠ 0

instance: Inv (Nonzero ℚ) := {
  inv := λ a ↦ ⟨inv a.property, inv_nonzero a.property⟩
}

-- a/b ≤ c/d if ... abd^2 ≤ cb^2d
-- todo; implement a Pow instance.
def ℚ.le (a b: ℚ): Prop :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ a₁ * a₂ * b₂ * b₂ ≤ b₁ * b₂ * a₂ * a₂)
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    --apply Quotient.sound
    simp
    sorry
  )

instance: LE ℚ := ⟨ℚ.le⟩

instance {a b: ℚ}: Decidable (a ≤ b) := sorry

def ℚ.abs (a: ℚ): ℚ :=
  if 0 ≤ a then a else -a
