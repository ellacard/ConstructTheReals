import ConstructTheReals.Set

variable {α: Type u₁} {β: Type u₂}

-- Pointed set

class Pointed (α: Type u) where
  unit: α

export Pointed (unit)
namespace Pointed
scoped instance [Pointed α]: Zero α := ⟨unit⟩
end Pointed

class Pointed.sub (P: Pointed α) (S: Set α): Prop where
  unit_mem: 0 ∈ S



-- Magma

class Magma (α: Type u) where
  op: α → α → α

class CommMagma (α: Type u) extends Magma α where
  comm: Commutative op

export Magma (op)
namespace Magma
scoped instance [Magma α]: Add α := ⟨op⟩
end Magma
open Magma

theorem op_comm [CommMagma α] (a b: α): a + b = b + a := by
  exact CommMagma.comm a b

class Magma.sub (M: Magma α) (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → a + b ∈ S



/-

A monoid is a set with:
- a "pointed" structure, i.e. a distinguished point 0,
- a magma structure, i.e. a binary operation.

where:
- 0 is an identity for the operation,
- the operation is associative.

-/

class Monoid (α: Type u) extends Pointed α, Magma α where
  identity: Identity op unit
  assoc: Associative op

class CommMonoid (α: Type u) extends Monoid α, CommMagma α

-- Introduce `+` and `0` notation to the monoid namespace.

namespace Monoid
scoped instance [Magma α]: Add α := ⟨op⟩
scoped instance [Pointed α]: Zero α := ⟨Pointed.unit⟩

end Monoid
open Monoid

-- Unpack axioms with notation.

theorem op_unit_left [Monoid α] (a: α): 0 + a = a := by
  exact Monoid.identity.left a

theorem op_unit_right [Monoid α] (a: α): a + 0 = a := by
  exact Monoid.identity.right a

theorem op_assoc [Monoid α] (a b c: α): a + b + c = a + (b + c) := by
  exact Monoid.assoc a b c

def inverses [Monoid α] (a b: α): Prop :=
  Inverses op a b unit

def inverses_iff [Monoid α] (a b: α): inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

theorem inverses_unique [Monoid α] {a b b': α}
  (h: inverses a b) (h': inverses a b'): b = b' := by
  simp_all [inverses_iff]
  calc
    b = b + 0        := by rw [op_unit_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [op_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [op_unit_left]


theorem left_right_inverse_eq [Monoid α] {a b c: α}
  (h₁: a + b = 0) (h₂: b + c = 0): a = c := by
  calc
    a = a + 0        := by rw [op_unit_right]
    _ = a + (b + c) := by rw [h₂]
    _ = (a + b) + c := by rw [op_assoc]
    _ = 0 + c       := by rw [h₁]
    _ = c           := by rw [op_unit_left]

-- A submonoid is a subset which contains the unit and is closed under the operation.

class Monoid.sub (M: Monoid α) (S: Set α) extends
  toPointedSub: M.toPointed.sub S,
  toMagmaSub: M.toMagma.sub S

theorem Monoid.full_sub (M: Monoid α): M.sub (Set.full α) := {
  unit_mem := trivial
  op_closed := by
    intros
    trivial
}

-- Zero sum free monoid

def Monoid.zerosumfree (M: Monoid α): Prop :=
  ∀ a b: α, a + b = 0 → a = 0 ∧ b = 0



-- Monoid simplifier. Useful for `calc` steps.

theorem op_swap [CommMonoid α] {a b c: α}: (a + b) + c = (a + c) + b := by
  rw [op_assoc]
  rw [op_comm b c]
  rw [←op_assoc]

theorem op_swap' [CommMonoid α] {a b c: α}: (a + b) + c = (b + a) + c := by
  rw [op_comm a b]

macro "simp_monoid": tactic =>
  `(tactic| try simp [←op_assoc, op_swap, op_swap'])
