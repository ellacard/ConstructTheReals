/-

Define the natural numbers ℕ as an inductive type.

Properties of ℕ:
- (ℕ, +) is a cancellative commutative monoid
- (ℕ, +, *) is a commutative semiring
- (ℕ, ≤) is a lattice

-/

inductive ℕ where
| zero: ℕ
| next: ℕ → ℕ

namespace ℕ

instance: Zero ℕ := ⟨zero⟩

def one: ℕ :=
  next 0

instance: One ℕ := ⟨one⟩

theorem zero_eq: zero = 0 := by
  rfl

theorem one_eq: one = 1 := by
  rfl

theorem one_eq_next_zero: next 0 = 1 := by
  rfl



-- Define addition.

def add (a b: ℕ): ℕ :=
  match b with
  | 0 => a
  | next p => next (add a p)

instance: Add ℕ := ⟨add⟩

-- Addition theorems.

theorem next_eq_iff {a b: ℕ}: a.next = b.next ↔ a = b := by
  exact Eq.to_iff (next.injEq a b)

theorem add_next_right {a b: ℕ}: a + b.next = (a + b).next := by
  induction a with
  | zero => rfl
  | next p hp => rfl

theorem add_next_left {a b: ℕ}: a.next + b = (a + b).next := by
  induction b with
  | zero => rfl
  | next p hp =>
    repeat rw [add_next_right]
    rw [hp]

theorem add_zero_right (a: ℕ): a + 0 = a := by
  rfl

theorem add_zero_left (a: ℕ): 0 + a = a := by
  induction a with
  | zero => rfl
  | next p hp =>
    rw [add_next_right, hp]

theorem add_comm (a b: ℕ): a + b = b + a := by
  induction a with
  | zero =>
    rw [zero_eq, add_zero_left, add_zero_right]
  | next p hp =>
    rw [add_next_left, add_next_right, hp]

theorem add_assoc (a b c: ℕ): a + b + c = a + (b + c) := by
  induction a with
  | zero =>
    rw [zero_eq]
    repeat rw [add_zero_left]
  | next p hp =>
    repeat rw [add_next_left]
    rw [hp]

theorem add_cancel_right {a b: ℕ} (c: ℕ) (h: a + c = b + c): a = b := by
  induction c with
  | zero =>
    repeat rw [add_zero_right] at h
    exact h
  | next p hp =>
    apply hp
    exact next_eq_iff.mp h

theorem add_cancel_left (a: ℕ) {b c: ℕ} (h: a + b = a + c): b = c := by
  induction a with
  | zero =>
    rw [zero_eq] at h
    repeat rw [add_zero_left] at h
    exact h
  | next p hp =>
    apply hp
    repeat rw [add_next_left] at h
    exact next_eq_iff.mp h

theorem add_zero_eq_zero {a b: ℕ} (h: a + b = 0): a = 0 := by
  induction b with
  | zero => exact h
  | next p hp => contradiction



-- Define multiplication.

def mul (a b: ℕ): ℕ :=
  match b with
  | 0 => 0
  | next p => (mul a p) + a

instance: Mul ℕ := ⟨mul⟩

-- Multiplication theorems.

theorem mul_one_right (a: ℕ): a * 1 = a := by
  induction a with
  | zero => rfl
  | next p hp => exact Eq.symm (congrArg next (Eq.symm hp))

theorem mul_one_left (a: ℕ): 1 * a = a := by
  induction a with
  | zero => rfl
  | next p hp => exact Eq.symm (congrArg next (Eq.symm hp))

theorem mul_zero_right (a: ℕ): a * 0 = 0 := by
  induction a with
  | zero => rfl
  | next p hp => exact hp

theorem mul_zero_left (a: ℕ): 0 * a = 0 := by
  induction a with
  | zero => rfl
  | next p hp => exact hp

theorem mul_next_right (a b: ℕ): a * b.next = a + a * b := by
  induction b with
  | zero =>
    rw [zero_eq, one_eq_next_zero, mul_one_right, mul_zero_right, add_zero_right]
  | next p hp =>
    rw [hp]
    have : a * p.next.next = a * p.next + a := by rfl
    rw [this]
    rw [hp]
    exact Eq.symm (add_comm a (a + a * p))

theorem mul_next_left (a b: ℕ): a.next * b = a * b + b := by
  induction b with
  | zero =>
    rw [zero_eq]
    repeat rw [mul_zero_right]
    rw [add_zero_right]
  | next p hp =>
    repeat rw [mul_next_right]
    repeat rw [add_next_left, add_next_right]
    rw [hp]
    apply next_eq_iff.mpr
    rw [add_assoc]

theorem mul_comm (a b: ℕ): a * b = b * a := by
  induction a with
  | zero => rw [zero_eq, mul_zero_left, mul_zero_right]
  | next p hp => rw [mul_next_left, mul_next_right, hp, add_comm]

theorem distrib_right (a b c: ℕ): (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
    rw [zero_eq]
    repeat rw [mul_zero_right]
    rw [add_zero_right]
  | next p hp =>
    repeat rw [mul_next_right]
    calc
      a + b + (a + b) * p
      _ = a + b + (a * p + b * p)   := by rw [hp]
      _ = a + (b + (a * p + b * p)) := by rw [add_assoc]
      _ = a + ((a * p + b * p) + b) := by simp [add_comm]
      _ = a + a * p + (b * p + b)   := by simp [add_assoc]
      _ = a + a * p + (b + b * p)   := by simp [add_comm]

theorem distrib_left (a b c: ℕ): a * (b + c) = a * b + a * c := by
  rw [mul_comm, mul_comm a b, mul_comm a c]
  exact distrib_right b c a

theorem mul_assoc (a b c: ℕ): a * b * c = a * (b * c) := by
  induction c with
  | zero =>
    rw [zero_eq]
    repeat rw [mul_zero_right]
  | next p hp =>
    repeat rw [mul_next_right]
    rw [hp]
    rw [distrib_left a b (b * p)]

theorem mul_cancel_right {a b c: ℕ} (h: a * c = b * c) (hc: c ≠ 0): a = b := by
  sorry

theorem mul_cancel_left {a b c: ℕ} (h: a * b = a * c) (ha: a ≠ 0): b = c := by
  rw [mul_comm a b, mul_comm a c] at h
  exact mul_cancel_right h ha



-- Define an order ≤ on ℕ.

def le (a b: ℕ): Prop :=
  ∃ d, a + d = b

instance: LE ℕ := ⟨le⟩

instance {X: Type u} [LE X]: LT X := {
  lt := λ x y ↦ x ≤ y ∧ ¬ y ≤ x
}

-- Order theorems.

theorem le_refl (a: ℕ): a ≤ a := by
  exists 0

theorem le_trans {a b c: ℕ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  have ⟨d₁, hd₁⟩ := h₁
  have ⟨d₂, hd₂⟩ := h₂
  exists d₁ + d₂
  rw [←hd₂, ←hd₁, add_assoc]

theorem le_antisymm {a b: ℕ} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  have ⟨d₁, hd₁⟩ := h₁
  have ⟨d₂, hd₂⟩ := h₂
  have: a = a + (d₁ + d₂) := by calc
    a
    _ = b + d₂ := by rw [←hd₂]
    _ = a + d₁ + d₂ := by rw [←hd₁]
    _ = a + (d₁ + d₂) := by rw [add_assoc]
  have: d₁ + d₂ = 0 := by
    apply add_cancel_left (a := a)
    apply Eq.symm
    exact this
  have hd₁': d₁ = 0 := by
    exact add_zero_eq_zero this
  have hd₂': d₂ = 0 := by
    rw [add_comm] at this
    exact add_zero_eq_zero this
  rw [←hd₂, ←hd₁, hd₁', hd₂']
  repeat rw [add_zero_right]

theorem le_total (a b: ℕ): a ≤ b ∨ b ≤ a := by
  sorry

theorem le_bottom (a: ℕ): 0 ≤ a := by
  exists a
  exact add_zero_left a

theorem le_add {a b c: ℕ} (h: a ≤ b): a + c ≤ b + c := by
  have ⟨t, ht⟩ := h
  exists t
  rw [←ht, add_assoc, add_comm c t, ←add_assoc]

instance: DecidableEq ℕ := sorry
instance: ∀ a b: ℕ, Decidable (a ≤ b) := sorry

theorem not_le_lt {a b: ℕ} (h: ¬a ≤ b): b < a := by
  sorry

theorem not_le_le {a b: ℕ} (h: ¬a ≤ b): b ≤ a := by
  exact (not_le_lt h).left

def min (a b: ℕ): ℕ :=
  if a ≤ b then a else b

def max (a b: ℕ): ℕ :=
  if a ≤ b then b else a

def min_symm (a b: ℕ): min a b = min b a := by
  by_cases h: a ≤ b <;> simp_all [min]
  exact le_antisymm h
  intro
  have := not_le_le h
  contradiction

theorem max_le_left (a b: ℕ): a ≤ max a b := by
  by_cases a ≤ b <;> simp_all [max]
  exact le_refl a

theorem max_le_right (a b: ℕ): b ≤ max a b := by
  by_cases h: a ≤ b <;> simp_all [max]
  exact le_refl b
  exact not_le_le h

theorem max_lub (a b c: ℕ) (h₁: a ≤ b) (h₂: b ≤ c): max a b ≤ c := by
  sorry



-- More theorems about ℕ

theorem one_nonzero: (1: ℕ) ≠ 0 := by
  intro
  contradiction

instance: Max ℕ := ⟨sorry⟩
