import ConstructTheReals.Simple.Rational

/-

Define the real numbers ℝ as the quotient on the set of cauchy sequences ℕ → ℚ by the relation
  (a_n) ~ (b_n) ↔ |a_n - b_n| converges to 0
thus completing ℚ.

Properties of ℝ:

-/

namespace ℚ

def dist (a b: ℚ): ℚ :=
  abs (a - b)

def converges_to (a: ℕ → ℚ) (L: ℚ): Prop :=
  ∀ r > 0, ∃ n, ∀ m ≥ n, dist (a m) L < r

def cauchy (a: ℕ → ℚ): Prop :=
  ∀ r > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (a m) (a n) < r

def cauchy_set: Set (ℕ → ℚ) :=
  λ a ↦ cauchy a

theorem dist_self_zero (a: ℚ): dist a a = 0 := by
  sorry

theorem dist_symm (a b: ℚ): dist a b = dist b a := by
  sorry

theorem triangle_inequality (a b c: ℚ): dist a c ≤ dist a b + dist b c := by
  sorry

end ℚ



-- Define the quotient on the set of cauchy sequences of rational numbers.

def ℝ: Type := @Quotient ℚ.cauchy_set {
  r := λ a b ↦ ℚ.converges_to (λ n ↦ ℚ.dist (a.val n) (b.val n)) 0
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

-- TODO:
-- Define 0 and 1.
-- Define addition.
-- Define subtraction.
-- Define multiplication.
-- Define division.
-- Define ≤.
