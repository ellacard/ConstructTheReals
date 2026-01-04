import ConstructTheReals.Relation
import ConstructTheReals.Ring

/-

Define the natural numbers ℕ as an inductive type.

Properties of ℕ:
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

theorem next_ne_zero (a: ℕ): a.next ≠ 0 := by
  intro h
  contradiction



-- Define addition.

def add (a b: ℕ): ℕ :=
  match b with
  | 0 => a
  | next p => next (add a p)

instance: Add ℕ := ⟨add⟩

theorem next_eq {a: ℕ}: a.next = a + 1 := by
  rfl

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

theorem mul_eq_zero {a b: ℕ} (h: a * b = 0): a = 0 ∨ b = 0 := by
  induction a with
  | zero => exact Or.inl rfl
  | next p hp =>
    rw [mul_next_left] at h
    have hpb : p * b = 0 := add_zero_eq_zero h
    have hb : b = 0 := by
      rw [hpb] at h
      rw [add_zero_left] at h
      exact h
    exact Or.inr hb

theorem mul_cancel_right {a b c: ℕ} (h: a * c = b * c) (hc: c ≠ 0): a = b := by
  sorry

theorem mul_cancel_left {a b c: ℕ} (h: a * b = a * c) (ha: a ≠ 0): b = c := by
  rw [mul_comm a b, mul_comm a c] at h
  exact mul_cancel_right h ha



-- Finally, define the commutative semiring on ℕ.

instance CommSemiring: CommSemiring ℕ := {
  add := add
  zero := zero
  add_assoc := add_assoc
  add_zero := ⟨add_zero_left, add_zero_right⟩
  add_comm := add_comm
  mul := mul
  one := one
  mul_assoc := mul_assoc
  mul_one := ⟨mul_one_left, mul_one_right⟩
  distrib := ⟨distrib_left, distrib_right⟩
  mul_comm := mul_comm
}



-- Define ≤.

def le (a b: ℕ): Prop :=
  ∃ d, a + d = b

instance: LE ℕ := ⟨le⟩

instance {X: Type u} [LE X]: LT X := {
  lt := λ x y ↦ x ≤ y ∧ x ≠ y
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

theorem le_bottom (a: ℕ): 0 ≤ a := by
  exists a
  exact add_zero_left a

theorem le_add {a b c: ℕ} (h: a ≤ b): a + c ≤ b + c := by
  have ⟨t, ht⟩ := h
  exists t
  rw [←ht, add_assoc, add_comm c t, ←add_assoc]

theorem le_add_left (a: ℕ) {b c: ℕ} (h: a + b ≤ a + c): b ≤ c := by
  have ⟨k, hk⟩ := h
  rw [add_assoc a b k] at hk
  have := add_cancel_left a hk
  exists k

theorem le_add_right {a b: ℕ} (c: ℕ) (h: a + c ≤ b + c): a ≤ b := by
  rw [add_comm a c, add_comm b c] at h
  exact le_add_left c h

theorem le_total (a b: ℕ): a ≤ b ∨ b ≤ a := by
  induction a with
  | zero => exact Or.inl (le_bottom b)
  | next p hp =>
    cases hp with
    | inl h =>
      have ⟨k, hk⟩ := h
      cases k with
      | zero =>
        apply Or.inr
        exists 1
        have : p + zero = p := rfl
        rw [this] at hk
        rw [←hk]
        exact next_eq
      | next k =>
        apply Or.inl
        exists k
        rw [add_next_left]
        rw [add_next_right] at hk
        exact hk
    | inr h =>
      apply Or.inr
      have ⟨k, hk⟩ := h
      exists k.next
      rw [add_next_right]
      rw [hk]

theorem not_le {a b: ℕ} (h: ¬a ≤ b): ∀ k, ¬a + k = b := by
  exact not_exists.mp h

theorem not_le_le {a b: ℕ} (h: ¬a ≤ b): b ≤ a := by
  cases le_total a b with
  | inl => contradiction
  | inr h' => exact h'

theorem not_le_lt {a b: ℕ} (h: ¬a ≤ b): b < a := by
  have ⟨k, hk⟩ := not_le_le h
  by_cases h₀: k = 0
  · have := not_le h 0
    rw [add_zero_right] at this
    rw [h₀, add_zero_right] at hk
    have: a = b := by exact Eq.symm hk
    contradiction
  · constructor
    · exists k
    · intro h'
      rw [←add_zero_right b] at h'
      have: b + k = b + 0 := by rw [hk, h']
      have: k = 0 := by rw [add_cancel_left b this]
      contradiction

instance: DecidableEq ℕ := sorry

instance: ∀ a b: ℕ, Decidable (a ≤ b) := sorry



-- Define min and max.

def min (a b: ℕ): ℕ :=
  if a ≤ b then a else b

instance: Min ℕ := ⟨min⟩

def max (a b: ℕ): ℕ :=
  if a ≤ b then b else a

instance: Max ℕ := ⟨max⟩

-- Min and max theorems.

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

theorem max_lub (a b c: ℕ) (h₁: a ≤ c) (h₂: b ≤ c): max a b ≤ c := by
  by_cases h: a ≤ b
  · rw [max, if_pos h]
    exact h₂
  · rw [max, if_neg h]
    exact h₁



-- Finally, define the lattice on ℕ.

instance Lattice: Lattice ℕ := {
  reflexive := le_refl
  transitive := @le_trans
  antisymmetric := @le_antisymm
  min := ℕ.min
  max := ℕ.max
  max_le_left := max_le_left
  max_le_right := max_le_right
  max_lub := sorry
  min_le_left := sorry
  min_le_right := sorry
  min_glb := sorry
}





/-

TODO
Subtraction of natural numbers, truncated at 0. If a result would be less than zero, then the result is zero.

-/

instance: Sub ℕ := {
  sub := sorry
}

-- TODO Additional natural number theorems.

theorem le_add_of_sub_le {a b c : ℕ} (h : a - b ≤ c) : a ≤ c + b := by
  sorry

theorem le_of_add_left_le {n m k : ℕ} (h : k + n ≤ m) : n ≤ m := by
  sorry

theorem le_sub_of_add_le {a b c : ℕ} (h : a + b ≤ c) : a ≤ c - b := by
  sorry

theorem sub_add_cancel {n m : ℕ} (h : m ≤ n) : n - m + m = n := by
  sorry

theorem le_of_not_ge {a b : ℕ} : ¬a ≥ b → a ≤ b := by
  sorry
