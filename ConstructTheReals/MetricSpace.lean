import ConstructTheReals.Monoid
import ConstructTheReals.Natural

variable {X: Type u} {D: Type v}

open Monoid

/-

A generalized metric space consists of:

- a set X
- a set D with "distance space" structure:
  · ordering ≤
  · zero 0
  · addition +
  · "completition" ie. ability to divide by 2
- a metric d: X × X → D, where:
  . 0 ≤ d(x, y)
  · d(x, y) = 0 ↔ x = y
  · d(x, y) = d(y, x)
  · Triangle inequality: d(x, z) ≤ d(x, y) + d(x, z)

-/

-- First, define a "distance space" as a set with an order, zero element, and addition operation

class DistanceSpace (D: Type v) where
  le: D → D → Prop
  le_refl: ∀ d, le d d
  le_trans: ∀ d₁ d₂ d₃, le d₁ d₂ → le d₂ d₃ → le d₁ d₃
  le_antisymm: ∀ d₁ d₂, le d₁ d₂ → le d₂ d₁ → d₁ = d₂
  zero: D
  add: D → D → D
  add_assoc: Associative add
  add_zero: Identity add zero
  le_add: ∀ d₁ d₂ d, le d₁ d₂ ↔ le (add d₁ d) (add d₂ d)
  complete: ∀ d: D, (le zero d ∧ zero ≠ d) → ∃ r, (le zero r ∧ zero ≠ r) ∧ le (add r r) d

instance [DistanceSpace D]: LE D := ⟨DistanceSpace.le⟩

instance [DistanceSpace D]: Monoid D := {
  op := DistanceSpace.add
  unit := DistanceSpace.zero
  identity := DistanceSpace.add_zero
  assoc := DistanceSpace.add_assoc
}

theorem distance_complete [DistanceSpace D]: ∀ d: D, 0 < d → ∃ r, 0 < r ∧ r + r ≤ d := by
  exact DistanceSpace.complete



-- Then, define a generalized metric space

class Metric (X: Type u) (D: Type v) [DistanceSpace D] where
  distance: X → X → D
  distance_le: ∀ x y, 0 ≤ distance x y
  distance_zero_iff: ∀ x y, distance x y = 0 ↔ x = y
  distance_symm: ∀ x y, distance x y = distance y x
  distance_triangle: ∀ x y z, distance x z ≤ distance x y + distance y z

instance [DistanceSpace D] [Metric X D]: CoeFun (Metric X D) (λ _ ↦ X → X → D) := {
  coe _ := Metric.distance
}

variable [DistanceSpace D]

theorem distance_le [d: Metric X D]: ∀ x y, 0 ≤ d x y := by
  exact Metric.distance_le

theorem distance_zero_iff [d: Metric X D]: ∀ x y, d x y = 0 ↔ x = y := by
  exact Metric.distance_zero_iff

theorem distance_symm [d: Metric X D]: ∀ x y, d x y = d y x := by
  exact Metric.distance_symm

theorem distance_triangle [d: Metric X D]: ∀ x y z, d x z ≤ d x y + d y z := by
  exact Metric.distance_triangle

theorem dist_self_zero [d: Metric X D] (x: X): d x x = 0 := by
  apply (distance_zero_iff x x).mpr
  rfl

theorem not_lt_self (x: D): ¬(x < x) := by
  sorry

theorem le_add {x₁ x₂ y₁ y₂: D} (h₁: x₁ < y₁) (h₂: x₂ < y₂): x₁ + x₂ < y₁ + y₂ := by
  sorry

theorem le_lt_trans {x y z: D} (h₁: x ≤ y) (h₂: y < z): x < z := by
  sorry

theorem lt_le_trans {x y z: D} (h₁: x < y) (h₂: y ≤ z): x < z := by
  sorry

theorem not_lt {x y: D}: ¬x < y ↔ y ≤ x := by
  sorry



-- Sequences

def Sequence (X: Type u): Type u :=
  ℕ → X

def ConstantSequence (x: X): Sequence X :=
  λ _ ↦ x

def converges_to (d: Metric X D) (a: Sequence X) (x: X): Prop :=
  ∀ r, 0 < r → ∃ n, ∀ m, n ≤ m → d (a m) x < r

def convergent (d: Metric X D) (a: Sequence X): Prop :=
  ∃ x, converges_to d a x

theorem constant_sequence_converges (d: Metric X D) (x: X): converges_to d (ConstantSequence x) x := by
  intro r hr
  exists 0
  intros
  rw [ConstantSequence, dist_self_zero]
  exact hr

def tail (s: Sequence X) (t: ℕ): Sequence X :=
  λ n ↦ s (n + t)

theorem converges_iff_tails_converge (d: Metric X D) (a: Sequence X) (x: X): converges_to d a x ↔ ∀ t, converges_to d (tail a t) x := by
  constructor
  · intro h t r hr
    have ⟨n, hn⟩ := h r hr
    exists n - t
    intro m hm
    apply hn (m + t)
    exact ℕ.le_add_of_sub_le hm
  · intro h
    exact h 0

theorem converges_iff_tail_converges (d: Metric X D) (a: Sequence X) (x: X): converges_to d a x ↔ ∃ t, converges_to d (tail a t) x := by
  constructor
  · intro h
    exists 0
  · intro ⟨t, ht⟩ r hr
    have ⟨n, hn⟩ := ht r hr
    exists n + t
    intro m hm
    simp [tail] at hn
    have := hn (m - t) (ℕ.le_sub_of_add_le hm)
    rw [ℕ.sub_add_cancel (ℕ.le_of_add_left_le hm)] at this
    exact this



-- Cauchy sequences

def Cauchy (d: Metric X D) (a: Sequence X): Prop :=
  ∀ r, 0 < r → ∃ N, ∀ m n, N ≤ m → N ≤ n → d (a m) (a n) < r

theorem cauchy_if_convergent {d: Metric X D} {a: Sequence X} (h: convergent d a): Cauchy d a := by
  intro r₀ hr₀
  have ⟨x, hx⟩ := h
  have ⟨r, hr₁, hr₂⟩ := distance_complete r₀ hr₀
  have ⟨N, hN⟩ := hx r hr₁
  exists N
  intro m n hm hn
  have dm := hN m hm
  have dn := hN n hn
  rw [d.distance_symm] at dn
  have := le_lt_trans (d.distance_triangle (a m) x (a n)) (le_add dm dn)
  exact lt_le_trans this hr₂

theorem constant_sequence_cauchy {d: Metric X D} {x: X}: Cauchy d (ConstantSequence x) := by
  have: convergent d (ConstantSequence x) := by
    exists x
    exact constant_sequence_converges d x
  exact cauchy_if_convergent this



-- Completion of a metric space via the quotient on cauchy sequences

def CauchySet (d: Metric D D): Set (ℕ → D) :=
  λ a ↦ Cauchy d a

def CauchyRelation (d: Metric D D): Endorelation (CauchySet d) :=
  λ ⟨a, _⟩ ⟨b, _⟩ ↦ converges_to d (λ n ↦ d (a n) (b n)) 0

theorem CauchyRelation.equiv (d: Metric D D): Equivalence (CauchyRelation d) := {
  refl := by
    intro _ _ hr
    exists 0
    intro _ _
    simp [dist_self_zero]
    exact hr
  symm := by
    intro _ _ h r hr
    have ⟨n, hn⟩ := h r hr
    exists n
    intro m hm
    simp [d.distance_symm]
    --exact hn m hm
    sorry
  trans := by
    intro a b c h₁ h₂
    intro r hr
    have ⟨r₀, hr₁, hr₂⟩ := distance_complete r hr
    have ⟨n₁, hn₁⟩ := h₁ r₀ hr₁
    have ⟨n₂, hn₂⟩ := h₂ r₀ hr₁
    exists max n₁ n₂
    intro m hm
    have h₁' := hn₁ m (ℕ.le_trans (ℕ.max_le_left n₁ n₂) hm)
    have h₂' := hn₂ m (ℕ.le_trans (ℕ.max_le_right n₁ n₂) hm)
    simp at h₁' h₂'
    sorry
}

def CauchyRelation.quotient (d: Metric D D): Type v :=
  Quotient ⟨CauchyRelation d, CauchyRelation.equiv d⟩

def Complete (d: Metric X D): Prop :=
  ∀ a, Cauchy d a → convergent d a
