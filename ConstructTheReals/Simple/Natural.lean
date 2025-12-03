

/-

Construction of the ℕ numbers.

Want to show:
1. (additive structure)
  - commutative monoid wrt. addition
  - cancellative
2. (multiplicative structure)
  - commutative monoid wrt. multiplication
  - cancellative wrt. nonzero elements
(together 2 and 3 make a commutative semiring)
3. (order structure)
  - partial order: reflexive, transitive, antisymmetric
  - total
  - a lattice (has max/join and min/meet)
  - zero is a bottom element
  - every nonempty set has infimum
  - every set bounded above has supremum

Notes:
- Could use an ordered monoid with ⊥ = 0?

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



-- Show (ℕ, +) is a cancellative commutative monoid.

def add (a b: ℕ): ℕ :=
  match b with
  | 0 => a
  | next p => next (add a p)

instance: Add ℕ := ⟨add⟩

theorem add_next_left {a b: ℕ}: a.next + b = (a + b).next := by
  induction b with
  | zero => rfl
  | next p hp =>
    sorry

theorem add_next_right {a b: ℕ}: a + b.next = (a + b).next := by
  induction a with
  | zero => rfl
  | next p hp =>
    sorry

theorem next_eq_iff {a b: ℕ}: a = b ↔ a.next = b.next := by
  constructor
  · intro h
    exact congrArg next h
  · intro h
    sorry

theorem add_zero_left (a: ℕ): 0 + a = a := by
  induction a with
  | zero => rfl
  | next p hp =>
    rw [add_next_right, hp]

theorem add_zero_right (a: ℕ): a + 0 = a := by
  rfl

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

theorem add_cancel_left (a: ℕ) {b c: ℕ} (h: a + b = a + c): b = c := by
  induction a with
  | zero =>
    rw [zero_eq] at h
    repeat rw [add_zero_left] at h
    exact h
  | next p hp =>
    apply hp
    repeat rw [add_next_left] at h
    exact next_eq_iff.mpr h

theorem add_cancel_right {a b: ℕ} (c: ℕ) (h: a + c = b + c): a = b := by
  induction c with
  | zero =>
    repeat rw [add_zero_right] at h
    exact h
  | next p hp =>
    apply hp
    exact next_eq_iff.mpr h

theorem add_zero_eq_zero {a b: ℕ} (h: a + b = 0): a = 0 := by
  induction b with
  | zero => exact h
  | next p hp => contradiction



-- Show (ℕ, *) is a commutative monoid.

def mul (a b: ℕ): ℕ :=
  match b with
  | 0 => 0
  | next p => (mul a p) + a

instance: Mul ℕ := ⟨mul⟩

theorem mul_one_left (a: ℕ): 1 * a = a := by
  induction a with
  | zero => rfl
  | next p hp => exact Eq.symm (congrArg next (Eq.symm hp))

theorem mul_one_right (a: ℕ): a * 1 = a := by
  induction a with
  | zero => rfl
  | next p hp => exact Eq.symm (congrArg next (Eq.symm hp))

theorem mul_zero_left (a: ℕ): 0 * a = 0 := by
  induction a with
  | zero => rfl
  | next p hp => exact hp

theorem mul_zero_right (a: ℕ): a * 0 = 0 := by
  induction a with
  | zero => rfl
  | next p hp => exact hp

theorem mul_next_left (a b: ℕ): a.next * b = a * b + b := by
  sorry

theorem mul_next_right (a b: ℕ): a * b.next = a + a * b := by
  sorry

theorem mul_assoc (a b c: ℕ): a * b * c = a * (b * c) := by
  sorry

theorem mul_comm (a b: ℕ): a * b = b * a := by
  induction a with
  | zero => rw [zero_eq, mul_zero_left, mul_zero_right]
  | next p hp => rw [mul_next_left, mul_next_right, hp, add_comm]

theorem mul_cancel_left {a b c: ℕ} (h: a * b = a * c) (ha: a ≠ 0): b = c := by
  induction a with
  | zero => contradiction
  | next p hp =>
    sorry

theorem mul_cancel_right {a b c: ℕ} (h: a * c = b * c) (hc: c ≠ 0): a = b := by
  induction c with
  | zero => contradiction
  | next p hp =>
    sorry



-- Show (ℕ, +, *) is a semiring

theorem distrib_left (a b c: ℕ): a * (b + c) = a * b + a * c := by
  induction a with
  | zero =>
    rw [zero_eq]
    repeat rw [mul_zero_left]
    rw [add_zero_left]
  | next p hp =>
    repeat rw [mul_next_left]
    rw [hp]
    sorry

theorem distrib_right (a b c: ℕ): (a + b) * c = a * c + b * c := by
  induction c with
  | zero =>
    rw [zero_eq]
    repeat rw [mul_zero_right]
    rw [add_zero_right]
  | next p hp =>
    repeat rw [mul_next_right]
    rw [hp]
    sorry



-- Show (ℕ, ≤) is a lattice.

def le (a b: ℕ): Prop :=
  ∃ d, a + d = b

instance: LE ℕ := ⟨le⟩

instance {X: Type u} [LE X]: LT X := {
  lt := λ x y ↦ x ≤ y ∧ ¬ y ≤ x
}

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

theorem not_le_lt {a b: ℕ} (h: ¬ a ≤ b): b < a := by
  sorry

theorem not_le_le {a b: ℕ} (h: ¬ a ≤ b): b ≤ a := by
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

theorem max_lub (a b c: ℕ) (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry
