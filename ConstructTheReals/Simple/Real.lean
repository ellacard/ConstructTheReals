import ConstructTheReals.Simple.Rational

/-

Define the real numbers ℝ as the quotient on the set of cauchy sequences ℕ → ℚ by the relation
  (a_n) ~ (b_n) ↔ |a_n - b_n| converges to 0
thus completing ℚ.

Properties of ℝ:

-/

namespace ℚ

-- Metric properties.

def dist (a b: ℚ): ℚ :=
  abs (a - b)

theorem dist_self_zero (a: ℚ): dist a a = 0 := by
  sorry

theorem dist_symm (a b: ℚ): dist a b = dist b a := by
  sorry

theorem triangle_inequality (a b c: ℚ): dist a c ≤ dist a b + dist b c := by
  sorry

-- Sequences.

def converges_to (a: ℕ → ℚ) (L: ℚ): Prop :=
  ∀ r > 0, ∃ n, ∀ m ≥ n, dist (a m) L < r

def cauchy (a: ℕ → ℚ): Prop :=
  ∀ r > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (a m) (a n) < r

def cauchy_set: Set (ℕ → ℚ) :=
  λ a ↦ cauchy a

def constant_sequence (q: ℚ): cauchy_set :=
  ⟨λ _ ↦ q, by sorry⟩

def cauchy_add (a b: cauchy_set): cauchy_set :=
  ⟨λ n ↦ a.val n + b.val n, by sorry⟩

def cauchy_neg (a: cauchy_set): cauchy_set :=
  ⟨λ n ↦ -(a.val n), by sorry⟩

def cauchy_mul (a b: cauchy_set): cauchy_set :=
  ⟨λ n ↦ a.val n * b.val n, by sorry⟩

end ℚ



-- Define the quotient on the set of cauchy sequences of rational numbers.

def ℝ.relation: ℚ.cauchy_set → ℚ.cauchy_set → Prop :=
  λ a b ↦ ℚ.converges_to (λ n ↦ ℚ.dist (a.val n) (b.val n)) 0

def ℝ: Type := @Quotient ℚ.cauchy_set {
  r := ℝ.relation
  iseqv := {
    refl := by
      intro a r hr
      exists 0
      intro m hm
      simp
      repeat rw [ℚ.dist_self_zero]
      exact hr
    symm := by
      intro a b h r hr
      have ⟨n, hn⟩ := h r hr
      exists n
      intro m hm
      have h' := hn m hm
      simp at h' ⊢
      rw [ℚ.dist_symm (b.val m)]
      exact h'
    trans := by
      intro a b c h₁ h₂ r₀ hr
      have ⟨n₁, hn₁⟩ := h₁ r₀ hr
      have ⟨n₂, hn₂⟩ := h₂ r₀ hr
      exists max n₁ n₂
      intro m hm
      simp_all
      sorry
  }
}

namespace ℝ

instance: HasEquiv ℚ.cauchy_set := ⟨ℝ.relation⟩

theorem equiv_iff (a b: ℚ.cauchy_set): a ≈ b ↔ ℚ.converges_to (λ n ↦ ℚ.dist (a.val n) (b.val n)) 0 := by
  rfl



-- Embedding of ℚ in ℝ.

instance: Coe ℚ ℝ := ⟨λ q ↦ Quotient.mk _ (ℚ.constant_sequence q)⟩



-- Define 0 and 1.

def zero: ℝ :=
  Quotient.mk _ (ℚ.constant_sequence 0)

instance: Zero ℝ := ⟨zero⟩

def one: ℝ :=
  Quotient.mk _ (ℚ.constant_sequence 1)

instance: One ℝ := ⟨one⟩



-- Define addition.

def add (a b: ℝ): ℝ :=
  Quotient.liftOn₂ a b (λ a b ↦ Quotient.mk _ (ℚ.cauchy_add a b))
  ( by
    intro a b c d h h'
    apply Quotient.sound
    simp [equiv_iff]
    sorry
  )

instance: Add ℝ := ⟨add⟩



-- Define subtraction.

def neg (a: ℝ): ℝ :=
  Quotient.liftOn a (λ a ↦ Quotient.mk _ (ℚ.cauchy_neg a))
  ( by
    intro a b h
    apply Quotient.sound
    simp [equiv_iff]
    sorry
  )

instance: Neg ℝ := ⟨neg⟩



-- Define multiplication.

def mul (a b: ℝ): ℝ :=
  Quotient.liftOn₂ a b (λ a b ↦ Quotient.mk _ (ℚ.cauchy_mul a b))
  ( by
    intro a b c d h h'
    apply Quotient.sound
    simp [equiv_iff]
    sorry
  )

instance: Mul ℝ := ⟨mul⟩



-- Define division.

def inv {a: ℝ} (ha: a ≠ 0): ℝ :=
  Quotient.liftOn a (λ a ↦ sorry)
  ( by sorry )

theorem inv_nonzero {a: ℝ} (ha: a ≠ 0): (inv ha) ≠ 0 := by
  sorry

instance: Inv (Nonzero ℝ) := {
  inv := λ a ↦ ⟨inv a.property, inv_nonzero a.property⟩
}

instance: Div ℝ := ⟨sorry⟩



-- Define ≤.

def le (a b: ℝ): Prop :=
  Quotient.liftOn₂ a b (λ a b ↦ sorry)
  ( by sorry )

instance: LE ℝ := ⟨le⟩



-- Addition theorems.

theorem add_comm (a b: ℝ): a + b = b + a := by
  sorry

theorem add_assoc (a b c: ℝ): a + b + c = a + (b + c) := by
  sorry

theorem add_zero_left (a: ℝ): 0 + a = a := by
  sorry

theorem add_zero_right (a: ℝ): a + 0 = a := by
  sorry

theorem add_left_neg (a: ℝ): -a + a = 0 := by
  sorry

theorem add_right_neg (a: ℝ): a + -a = 0 := by
  sorry



-- Multiplication theorems.

theorem mul_comm (a b: ℝ): a * b = b * a := by
  sorry

theorem mul_assoc (a b c: ℝ): a * b * c = a * (b * c) := by
  sorry

theorem mul_one_left (a: ℝ): 1 * a = a := by
  sorry

theorem mul_one_right (a: ℝ): a * 1 = a := by
  sorry

theorem mul_zero_left (a: ℝ): 0 * a = 0 := by
  sorry

theorem mul_zero_right (a: ℝ): a * 0 = 0 := by
  sorry

theorem distrib_left (a b c: ℝ): a * (b + c) = a * b + a * c := by
  sorry

theorem distrib_right (a b c: ℝ): (a + b) * c = a * c + b * c := by
  sorry



-- Subtraction theorems.

theorem neg_neg (a: ℝ): -(-a) = a := by
  sorry

theorem neg_zero: (-0: ℝ) = 0 := by
  sorry

theorem neg_add (a b: ℝ): -(a + b) = -a + -b := by
  sorry

theorem neg_mul_left (a b: ℝ): (-a) * b = -(a * b) := by
  sorry

theorem neg_mul_right (a b: ℝ): a * (-b) = -(a * b) := by
  sorry



-- Inverse theorems.

theorem mul_inv_cancel {a: ℝ} (ha: a ≠ 0): a * (inv ha) = 1 := by
  sorry

theorem inv_mul_cancel {a: ℝ} (ha: a ≠ 0): (inv ha) * a = 1 := by
  sorry

theorem inv_inv {a: ℝ} (ha: a ≠ 0) (ha': inv ha ≠ 0): inv ha' = a := by
  sorry



-- Order theorems.

theorem le_refl (a: ℝ): a ≤ a := by
  sorry

theorem le_trans {a b c: ℝ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem le_antisymm {a b: ℝ} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  sorry

theorem le_total (a b: ℝ): a ≤ b ∨ b ≤ a := by
  sorry

theorem add_le_add_left (a: ℝ) {b c: ℝ} (h: b ≤ c): a + b ≤ a + c := by
  sorry

theorem add_le_add_right {a b: ℝ} (c: ℝ) (h: a ≤ b): a + c ≤ b + c := by
  sorry

theorem mul_le_mul_left {a b: ℝ} (c: ℝ) (hc: 0 < c) (h: a ≤ b): c * a ≤ c * b := by
  sorry

theorem zero_le_one: (0: ℝ) ≤ 1 := by
  sorry



-- Additional theorems.

theorem one_ne_zero: (1: ℝ) ≠ 0 := by
  sorry

theorem no_zero_divisors {a b: ℝ}: (a ≠ 0 ∧ b ≠ 0) → a * b ≠ 0 := by
  sorry



-- Completeness properties.

theorem archimedean (a: ℝ): ∃ n: ℕ, a < n := by
  sorry

-- TODO least upper bound property
