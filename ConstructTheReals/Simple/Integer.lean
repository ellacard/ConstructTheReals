import ConstructTheReals.Logic
import ConstructTheReals.Natural

/-

Define the integers ℤ as the quotient on ℕ ⨯ ℕ by the relation
  (a₁, a₂) ~ (b₁, b₂) ↔ a₁ + b₂ = b₁ + a₂
thus adjoining additive inverses for every element of ℕ.

Then, lift the operations + and * and the order ≤ to ℤ.

Properties of ℤ:
- (ℤ, +) is a commutative group
- (ℤ, *) is a commutative monoid
- (ℤ, +, *) is an integral domain (a nonzero commutative ring with no zero divisors)
- <order>

-/

-- Define the quotient on ℕ ⨯ ℕ.

def ℤ.relation: ℕ × ℕ → ℕ × ℕ → Prop :=
  λ (a₁, a₂) (b₁, b₂) ↦ a₁ + b₂ = b₁ + a₂

def ℤ: Type := @Quotient (ℕ × ℕ) {
  r := ℤ.relation
  iseqv := {
    refl := by intro; rfl
    symm := Eq.symm
    trans := by
      intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
      simp [ℤ.relation]
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

instance: HasEquiv (ℕ × ℕ) := ⟨ℤ.relation⟩

theorem equiv_iff (a₁ a₂ b₁ b₂: ℕ): (a₁, a₂) ≈ (b₁, b₂) ↔ a₁ + b₂ = b₁ + a₂ := by
  rfl



-- Embedding of ℕ in ℤ.

instance: Coe ℕ ℤ := ⟨λ n ↦ Quotient.mk _ (n, 0)⟩



-- Define 0 and 1.

def zero: ℤ :=
  Quotient.mk _ (0, 0)

instance: Zero ℤ := ⟨zero⟩

def one: ℤ :=
  Quotient.mk _ (1, 0)

instance: One ℤ := ⟨one⟩



-- Define addition.

def add (a b: ℤ): ℤ :=
  Quotient.liftOn₂ a b (λ (a₁, a₂) (b₁, b₂) ↦ Quotient.mk _ (a₁ + b₁, a₂ + b₂))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    calc
      (a₁ + b₁) + (c₂ + d₂)
      _ = a₁ + (b₁ + c₂) + d₂   := by simp [ℕ.add_assoc]
      _ = a₁ + (c₂ + b₁) + d₂   := by simp [ℕ.add_comm]
      _ = (a₁ + c₂) + (b₁ + d₂) := by simp [ℕ.add_assoc]
      _ = (c₁ + a₂) + (d₁ + b₂) := by rw [h, h']
      _ = c₁ + (a₂ + d₁) + b₂   := by simp [ℕ.add_assoc]
      _ = c₁ + (d₁ + a₂) + b₂   := by simp [ℕ.add_comm]
      _ = (c₁ + d₁) + (a₂ + b₂) := by simp [ℕ.add_assoc]
  )

instance: Add ℤ := ⟨add⟩



-- Define subtraction.

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



-- Define multiplication.

def mul (a b: ℤ): ℤ :=
  Quotient.liftOn₂ a b (λ (a₁, a₂) (b₁, b₂) ↦ Quotient.mk _ (a₁ * b₁ + a₂ * b₂, a₁ * b₂ + a₂ * b₁))
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) h h'
    apply Quotient.sound
    simp [equiv_iff] at h h'
    calc
      (a₁ * b₁ + a₂ * b₂) + (c₁ * d₂ + c₂ * d₁)
      _ = (c₁ * d₁ + c₂ * d₂) + (a₁ * b₂ + a₂ * b₁) := by sorry
  )

instance: Mul ℤ := ⟨mul⟩



-- Define ≤.

def le (a b: ℤ): Prop :=
  Quotient.liftOn₂ a b (λ (a₁, a₂) (b₁, b₂) ↦ a₁ + b₂ ≤ b₁ + a₂)
  ( by
    intro (a₁, a₂) (b₁, b₂) (c₁, c₂) (d₁, d₂) hac hbd
    simp [equiv_iff] at hac hbd
    simp
    constructor
    · intro h
      apply ℕ.le_add_left a₂
      apply ℕ.le_add_right b₁
      have h': (a₁ + b₂) + (d₁ + c₂) ≤ (a₂ + b₁) + (d₁ + c₂) := by
        apply ℕ.le_add
        rw [ℕ.add_comm a₂ b₁]
        exact h
      calc
        a₂ + (c₁ + d₂) + b₁
        _ = (a₂ + c₁) + (d₂ + b₁) := by simp [ℕ.add_assoc]
        _ = (c₁ + a₂) + (b₁ + d₂) := by simp [ℕ.add_comm]
        _ = (a₁ + c₂) + (d₁ + b₂) := by rw [hac, hbd]
        _ = a₁ + ((c₂ + d₁) + b₂) := by simp [ℕ.add_assoc]
        _ = a₁ + (b₂ + (d₁ + c₂)) := by simp [ℕ.add_comm]
        _ = (a₁ + b₂) + (d₁ + c₂) := by simp [ℕ.add_assoc]
        _ ≤ (a₂ + b₁) + (d₁ + c₂) := by exact h'
        _ = a₂ + (b₁ + (d₁ + c₂)) := by simp [ℕ.add_assoc]
        _ = a₂ + ((d₁ + c₂) + b₁) := by simp [ℕ.add_comm]
        _ = a₂ + (d₁ + c₂) + b₁   := by simp [ℕ.add_assoc]
    · intro h
      apply ℕ.le_add_left c₂
      apply ℕ.le_add_right d₁
      have h': (c₁ + d₂) + (a₂ + b₁) ≤ (d₁ + c₂) + (a₂ + b₁) := by
        apply ℕ.le_add
        exact h
      calc
        c₂ + (a₁ + b₂) + d₁
        _ = (c₂ + a₁) + (b₂ + d₁)   := by simp [ℕ.add_assoc]
        _ = (a₁ + c₂) + (d₁ + b₂)   := by simp [ℕ.add_comm]
        _ = (c₁ + a₂) + (b₁ + d₂)   := by simp [hac, hbd]
        _ = c₁ + ((a₂ + b₁) + d₂)   := by simp [ℕ.add_assoc]
        _ = c₁ + (d₂ + (a₂ + b₁))   := by simp [ℕ.add_comm]
        _ = (c₁ + d₂) + (a₂ + b₁)   := by simp [ℕ.add_assoc]
        _ ≤ (d₁ + c₂) + (a₂ + b₁)   := by exact h'
        _ = (d₁ + (c₂ + (a₂ + b₁))) := by simp [ℕ.add_assoc]
        _ = ((c₂ + (b₁ + a₂)) + d₁) := by simp [ℕ.add_comm]
        _ = c₂ + (b₁ + a₂) + d₁     := by simp [ℕ.add_assoc]
  )

instance: LE ℤ := ⟨le⟩



-- Addition theorems.

theorem add_comm (a b: ℤ): a + b = b + a := by
  sorry

theorem add_assoc (a b c: ℤ): a + b + c = a + (b + c) := by
  sorry

theorem add_zero_left (a: ℤ): 0 + a = a := by
  refine Quotient.inductionOn a ?_
  intro _
  apply Quotient.sound
  simp [ℕ.add_zero_left]
  rfl

theorem add_zero_right (a: ℤ): a + 0 = a := by
  refine Quotient.inductionOn a ?_
  intro _
  apply Quotient.sound
  simp [ℕ.add_zero_right]
  rfl



-- Multiplication theorems.

theorem mul_comm (a b: ℤ): a * b = b * a := by
  refine Quotient.inductionOn₂ a b ?_
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
  apply Quotient.sound
  simp [equiv_iff]
  calc
    a₁ * b₁ + a₂ * b₂ + (b₁ * a₂ + b₂ * a₁)
  _ = b₁ * a₁ + b₂ * a₂ + (a₂ * b₁ + a₁ * b₂) := by simp [ℕ.mul_comm]
  _ = b₁ * a₁ + b₂ * a₂ + (a₁ * b₂ + a₂ * b₁) := by simp [ℕ.add_comm]

theorem mul_assoc {a b c: ℤ}: (a * b) * c = a * (b * c) := by
  refine Quotient.inductionOn₃ a b c ?_
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
  apply Quotient.sound
  simp [equiv_iff]
  calc
    (a₁ * b₁ + a₂ * b₂) * c₁ + (a₁ * b₂ + a₂ * b₁) * c₂ + (a₁ * (b₁ * c₂ + b₂ * c₁) + a₂ * (b₁ * c₁ + b₂ * c₂))
    _ = a₁ * (b₁ * c₁ + b₂ * c₂) + a₂ * (b₁ * c₂ + b₂ * c₁) + ((a₁ * b₁ + a₂ * b₂) * c₂ + (a₁ * b₂ + a₂ * b₁) * c₁) := by sorry

theorem mul_one_left (a: ℤ): 1 * a = a := by
  sorry

theorem mul_one_right (a: ℤ): a * 1 = a := by
  sorry

theorem mul_zero_left (a: ℤ): 0 * a = 0 := by
  refine Quotient.inductionOn a ?_
  intro _
  apply Quotient.sound
  simp [equiv_iff, ℕ.mul_zero_left, ℕ.add_zero_left]

theorem mul_zero_right {a: ℤ}: a * 0 = 0 := by
  refine Quotient.inductionOn a ?_
  intro _
  apply Quotient.sound
  simp [equiv_iff, ℕ.mul_zero_right, ℕ.add_zero_right]

theorem distrib_left (a b c: ℤ): a * (b + c) = a * b + a * c := by
  sorry

theorem distrib_right (a b c: ℤ): (a + b) * c = a * c + b * c := by
  sorry

theorem mul_cancel_left {a b c: ℤ} (h: a ≠ 0): a * b = a * c → b = c := by
  sorry

theorem mul_cancel_right {a b c: ℤ} (h: c ≠ 0): a * c = b * c → a = b := by
  intro h'
  rw [mul_comm a c, mul_comm b c] at h'
  exact mul_cancel_left h h'



-- Subtraction theorems.

theorem add_left_neg (a: ℤ): -a + a = 0 := by
  sorry

theorem add_right_neg (a: ℤ): a + -a = 0 := by
  sorry

theorem neg_neg (a: ℤ): -(-a) = a := by
  sorry

theorem neg_zero: (-0: ℤ) = 0 := by
  sorry

theorem neg_add (a b: ℤ): -(a + b) = -a + -b := by
  sorry

theorem neg_mul_left (a b: ℤ): (-a) * b = -(a * b) := by
  sorry

theorem neg_mul_right (a b: ℤ): a * (-b) = -(a * b) := by
  sorry



-- Order theorems.

theorem le_refl (a: ℤ): a ≤ a := by
  sorry

theorem le_trans {a b c: ℤ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem le_antisymm {a b: ℤ} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  sorry

theorem le_total (a b: ℤ): a ≤ b ∨ b ≤ a := by
  sorry

theorem add_le_add_left (a: ℤ) {b c: ℤ} (h: b ≤ c): a + b ≤ a + c := by
  sorry

theorem add_le_add_right {a b: ℤ} (c: ℤ) (h: a ≤ b): a + c ≤ b + c := by
  sorry

theorem mul_le_mul_nonneg {a b c: ℤ} (hc: 0 ≤ c) (h: a ≤ b): c * a ≤ c * b := by
  sorry

theorem zero_le_one: (0: ℤ) ≤ 1 := by
  sorry



-- More theorems and definitions.

theorem one_nonzero: (1: ℤ) ≠ 0 := by
  intro h
  have := Quotient.exact h
  contradiction

theorem no_zero_divisors {a b: ℤ}: (a ≠ 0 ∧ b ≠ 0) → a * b ≠ 0 := by
  apply contrapose
  simp
  intro h h'
  apply mul_cancel_left (a := a)
  · exact h'
  · rw [mul_zero_right]
    exact h
