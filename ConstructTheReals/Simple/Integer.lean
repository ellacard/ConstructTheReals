import ConstructTheReals.Natural

def ℤ: Type := @Quotient (ℕ × ℕ) {
  r := λ (a₁, a₂) (b₁, b₂) ↦ a₁ + b₂ = b₁ + a₂
  iseqv := {
    refl := by intro; rfl
    symm := Eq.symm
    trans := by
      intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
      simp
      intro h₁ h₂
      apply ℕ.add_cancel_left b₂
      apply ℕ.add_cancel_right b₁
      calc
        b₂ + (a₁ + c₂) + b₁
        _ = (b₂ + a₁) + (c₂ + b₁) := by simp [ℕ.add_assoc]
        _ = (a₁ + b₂) + (b₁ + c₂) := by simp [ℕ.add_comm]
        _ = (b₁ + a₂) + (c₁ + b₂) := by rw [h₁, h₂]
        _ = (b₁ + (a₂ + c₁)) + b₂ := by simp [ℕ.add_assoc]
        _ = b₂ + ((c₁ + a₂) + b₁) := by simp [ℕ.add_comm]
        _ = b₂ + (c₁ + a₂) + b₁   := by simp [ℕ.add_assoc]
  }
}

namespace ℤ

def zero: ℤ :=
  Quotient.mk _ (0, 0)

instance: Zero ℤ := ⟨zero⟩

def one: ℤ :=
  Quotient.mk _ (1, 0)

instance: One ℤ := ⟨one⟩

def add (a b: ℤ): ℤ :=
  Quotient.liftOn₂ a b (λ (a₁, a₂) (b₁, b₂) ↦ Quotient.mk _ (a₁ + b₁, a₂ + b₂))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    calc
      (a₁ + b₁) + (c₂ + d₂)
      _ = (a₁ + c₂) + (b₁ + d₂) := by sorry
      _ = (c₁ + a₂) + (d₁ + b₂) := by rw [h, h']
      _ = (c₁ + d₁) + (a₂ + b₂) := by sorry
  )

instance: Add ℤ := ⟨add⟩

def neg (a: ℤ): ℤ :=
  Quotient.liftOn a (λ (a₁, a₂) ↦ Quotient.mk _ (a₂, a₁))
  ( by
    intro (a₁, a₂) (b₁, b₂) h
    apply Quotient.sound
    calc
      a₂ + b₁
      _ = b₁ + a₂ := by rw [ℕ.add_comm]
      _ = a₁ + b₂ := by rw [h]
      _ = b₂ + a₁ := by rw [ℕ.add_comm]
  )

instance: Neg ℤ := ⟨neg⟩

instance {X: Type u} [Add X] [Neg X]: Sub X := {
  sub := λ x y ↦ x + -y
}

def mul (a b: ℤ): ℤ :=
  Quotient.liftOn₂ a b (λ (a₁, a₂) (b₁, b₂) ↦ Quotient.mk _ (a₁ * b₁ + a₂ * b₂, a₁ * b₂ + a₂ * b₁))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    calc
      (a₁ * b₁ + a₂ * b₂) + (c₁ * d₂ + c₂ * d₁)
      _ = (c₁ * d₁ + c₂ * d₂) + (a₁ * b₂ + a₂ * b₁) := by sorry
  )

instance: Mul ℤ := ⟨mul⟩

theorem add_zero_left (a: ℤ): 0 + a = a := by
  refine Quotient.inductionOn a ?_
  intro
  apply Quotient.sound
  simp [ℕ.add_zero_left]
  rfl
