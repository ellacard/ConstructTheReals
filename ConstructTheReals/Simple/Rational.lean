import ConstructTheReals.Simple.Integer

/-

Define the rationals ℚ as the quotient on ℤ ⨯ ℤ \ {0} by the relation
  (a₁, a₂) ~ (b₁, b₂) ↔ a₁ * b₂ = b₁ * a₂
thus adjoining multiplicative inverses for every nonzero element of ℤ.

Then, lift the operations + and * and the order ≤ to ℚ.

Properties of ℚ:
- (ℚ, +) is a commutative group
- (ℚ, *) is a commutative monoid
- (ℚ, +, *) is a field
- <order>

-/

def Set (α: Type u): Type u :=
  α → Prop

instance (α: Type u): CoeSort (Set α) (Type u) := ⟨Subtype⟩

def Nonzero (X: Type u) [Zero X]: Set X :=
  λ x ↦ x ≠ 0



-- Define the quotient on ℤ × ℤ \ {0}.

def ℚ.relation: (ℤ × Nonzero ℤ) → (ℤ × Nonzero ℤ) → Prop :=
  λ (a₁, a₂) (b₁, b₂) ↦ a₁ * b₂ = b₁ * a₂

def ℚ: Type := @Quotient (ℤ × Nonzero ℤ) {
  r := ℚ.relation
  iseqv := {
    refl := by intro; rfl
    symm := Eq.symm
    trans := by
      intro (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) (c₁, ⟨c₂, hc₂⟩)
      simp [ℚ.relation]
      intro h₁ h₂
      apply ℤ.mul_cancel_left hb₂
      calc
        b₂ * (a₁ * c₂)
        _ = (b₂ * a₁) * c₂ := by simp [ℤ.mul_assoc]
        _ = (a₁ * b₂) * c₂ := by simp [ℤ.mul_comm]
        _ = (b₁ * a₂) * c₂ := by rw [h₁]
        _ = c₂ * (b₁ * a₂) := by simp [ℤ.mul_comm]
        _ = (c₂ * b₁) * a₂ := by simp [ℤ.mul_assoc]
        _ = (b₁ * c₂) * a₂ := by simp [ℤ.mul_comm]
        _ = (c₁ * b₂) * a₂ := by rw [h₂]
        _ = (b₂ * c₁) * a₂ := by simp [ℤ.mul_comm]
        _ = b₂ * (c₁ * a₂) := by simp [ℤ.mul_assoc]
  }
}

namespace ℚ

instance: HasEquiv (ℤ × Nonzero ℤ) := ⟨ℚ.relation⟩

theorem equiv_iff (a₁ b₁: ℤ) (a₂ b₂: Nonzero ℤ): (a₁, a₂) ≈ (b₁, b₂) ↔ a₁ * b₂ = b₁ * a₂ := by
  rfl



-- Embedding of ℤ in ℚ.

instance: One (Nonzero ℤ) := ⟨1, ℤ.one_nonzero⟩

instance: Coe ℤ ℚ := ⟨λ z ↦ Quotient.mk _ (z, 1)⟩


-- Define 0 and 1.

def zero: ℚ :=
  Quotient.mk _ (0, 1)

instance: Zero ℚ := ⟨zero⟩

def one: ℚ :=
  Quotient.mk _ (1, 1)

instance: One ℚ := ⟨one⟩



-- Define addition.

def add (a b: ℚ): ℚ :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ Quotient.mk _ (a₁ * b₂ + b₁ * a₂, ⟨a₂ * b₂, ℤ.no_zero_divisors ⟨ha₂, hb₂⟩⟩))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    simp [equiv_iff] at h h' ⊢
    calc
      (a₁ * b₂ + b₁ * a₂) * (c₂ * d₂)
      _ = (c₁ * d₂ + d₁ * c₂) * (a₂ * b₂) := by sorry
  )

instance: Add ℚ := ⟨add⟩



-- Define subtraction.

def neg (a: ℚ): ℚ :=
  Quotient.liftOn a (λ (a₁, a₂) ↦ Quotient.mk _ (-a₁, a₂))
  ( by
    intro (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) h
    apply Quotient.sound
    simp [equiv_iff] at h ⊢
    calc
      (-a₁) * b₂
      _ = (-b₁) * a₂ := by sorry
  )

instance: Neg ℚ := ⟨neg⟩



-- Define multiplication.

def mul (a b: ℚ): ℚ :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ Quotient.mk _ (a₁ * b₁, ⟨a₂ * b₂, ℤ.no_zero_divisors ⟨ha₂, hb₂⟩⟩))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    simp [equiv_iff] at h h' ⊢
    calc
      (a₁ * b₁) * (c₂ * d₂)
      _ = (c₁ * d₁) * (a₂ * b₂) := sorry
  )

instance: Mul ℚ := ⟨mul⟩



-- Define division.

def inv {a: ℚ} (ha: a ≠ 0): ℚ :=
  Quotient.liftOn a (λ (a₁, ⟨a₂, ha₂⟩) ↦ Quotient.mk _ (a₂, ⟨a₁, sorry⟩))
  ( by
    intro (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) h
    apply Quotient.sound
    simp [equiv_iff] at h ⊢
    calc
      a₂ * b₁
      _ = b₂ * a₁ := by sorry
  )

theorem inv_nonzero {a: ℚ} (ha: a ≠ 0): (inv ha) ≠ 0 := by
  sorry

instance: Inv (Nonzero ℚ) := {
  inv := λ a ↦ ⟨inv a.property, inv_nonzero a.property⟩
}

instance: Div ℚ := ⟨sorry⟩



-- Define ≤.

def le (a b: ℚ): Prop :=
  Quotient.liftOn₂ a b (λ (a₁, ⟨a₂, ha₂⟩) (b₁, ⟨b₂, hb₂⟩) ↦ a₁ * a₂ * b₂ * b₂ ≤ b₁ * b₂ * a₂ * a₂)
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    simp [equiv_iff] at h h' ⊢
    sorry
  )

instance: LE ℚ := ⟨le⟩



-- Addition theorems.

theorem add_comm (a b: ℚ): a + b = b + a := by
  sorry

theorem add_assoc (a b c: ℚ): a + b + c = a + (b + c) := by
  sorry

theorem add_zero_left (a: ℚ): 0 + a = a := by
  sorry

theorem add_zero_right (a: ℚ): a + 0 = a := by
  sorry

theorem add_left_neg (a: ℚ): -a + a = 0 := by
  sorry

theorem add_right_neg (a: ℚ): a + -a = 0 := by
  sorry



-- Multiplication theorems.

theorem mul_comm (a b: ℚ): a * b = b * a := by
  sorry

theorem mul_assoc (a b c: ℚ): a * b * c = a * (b * c) := by
  sorry

theorem mul_one_left (a: ℚ): 1 * a = a := by
  sorry

theorem mul_one_right (a: ℚ): a * 1 = a := by
  sorry

theorem mul_zero_left (a: ℚ): 0 * a = 0 := by
  sorry

theorem mul_zero_right (a: ℚ): a * 0 = 0 := by
  sorry

theorem distrib_left (a b c: ℚ): a * (b + c) = a * b + a * c := by
  sorry

theorem distrib_right (a b c: ℚ): (a + b) * c = a * c + b * c := by
  sorry



-- Subtraction theorems.

theorem neg_neg (a: ℚ): -(-a) = a := by
  sorry

theorem neg_zero: (-0: ℚ) = 0 := by
  sorry

theorem neg_add (a b: ℚ): -(a + b) = -a + -b := by
  sorry

theorem neg_mul_left (a b: ℚ): (-a) * b = -(a * b) := by
  sorry

theorem neg_mul_right (a b: ℚ): a * (-b) = -(a * b) := by
  sorry



-- Inverse theorems.

theorem mul_inv_cancel {a: ℚ} (ha: a ≠ 0): a * (inv ha) = 1 := by
  sorry

theorem inv_mul_cancel {a: ℚ} (ha: a ≠ 0): (inv ha) * a = 1 := by
  sorry

theorem inv_inv {a: ℚ} (ha: a ≠ 0) (ha': inv ha ≠ 0): inv ha' = a := by
  sorry



-- Order theorems.

theorem le_refl (a: ℚ): a ≤ a := by
  sorry

theorem le_trans {a b c: ℚ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem le_antisymm {a b: ℚ} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  sorry

theorem le_total (a b: ℚ): a ≤ b ∨ b ≤ a := by
  sorry

theorem add_le_add_left (a: ℚ) {b c: ℚ} (h: b ≤ c): a + b ≤ a + c := by
  sorry

theorem add_le_add_right {a b: ℚ} (c: ℚ) (h: a ≤ b): a + c ≤ b + c := by
  sorry

theorem mul_le_mul_left {a b: ℚ} (c: ℚ) (hc: 0 < c) (h: a ≤ b): c * a ≤ c * b := by
  sorry

theorem zero_le_one: (0: ℚ) ≤ 1 := by
  sorry



-- More theorems and definitions.

theorem one_ne_zero: (1: ℚ) ≠ 0 := by
  sorry

theorem no_zero_divisors {a b: ℚ}: (a ≠ 0 ∧ b ≠ 0) → a * b ≠ 0 := by
  sorry

instance {a b: ℚ}: Decidable (a ≤ b) := sorry

def abs (a: ℚ): ℚ :=
  if 0 ≤ a then a else -a
