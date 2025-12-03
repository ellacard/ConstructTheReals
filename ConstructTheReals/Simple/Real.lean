import ConstructTheReals.Simple.Rational

namespace ℚ




instance: Zero ℚ :=
  sorry

instance: LE ℚ :=
  sorry

def dist (a b: ℚ): ℚ :=
  sorry

def converges_to (a: ℕ → ℚ) (L: ℚ): Prop :=
  ∀ r > 0, ∃ n, ∀ m ≥ n, dist (a m) L < r

def cauchy (a: ℕ → ℚ): Prop :=
  ∀ r > 0, ∃ N, ∀ m n, m ≥ N → n ≥ N → dist (a m) (a n) < r

def cauchy_set: Set (ℕ → ℚ) :=
  λ a ↦ cauchy a

end ℚ

def ℝ: Type := @Quotient ℚ.cauchy_set {
  r := λ a b ↦ ℚ.converges_to (λ n ↦ ℚ.dist (a.val n) (b.val n)) 0
  iseqv := {
    refl := by
      intro a
      -- Need dist(x, x) = 0 and also that constant sequence converges.
      sorry
    symm := by
      intro a b h
      -- Just need d(x, y) = d(y, x)
      sorry
    trans := by
      intro a b c h₁ h₂
      -- Uses the triangle inequality
      intro r hr
      -- Then use r/2...
      sorry
  }
}
