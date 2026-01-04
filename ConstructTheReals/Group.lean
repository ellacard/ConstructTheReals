import ConstructTheReals.Monoid

variable {α: Type u} {β: Type v} {γ: Type w}

/-

A group is a monoid where every element has an inverse.

-/

class Group (α: Type u) extends Monoid α where
  inv: α → α
  inverse: Inverse op inv unit

class CommGroup (α: Type u) extends Group α, CommMonoid α

-- Introduces notation +, 0, and - for groups.

export Group (inv)
namespace Group

scoped instance [Magma α]: Add α := ⟨op⟩
scoped instance [Pointed α]: Zero α := ⟨unit⟩
scoped instance [Group α]: Neg α := ⟨inv⟩
def opinv [Group α] (a b: α): α := a + -b
scoped instance [Group α]: Sub α := ⟨opinv⟩

end Group
open Group

-- Unpacking axioms with notation.

theorem op_inv_left [Group α] (a: α): -a + a = 0 := by
  exact Group.inverse.left a

theorem op_inv_right [Group α] (a: α): a + -a = 0 := by
  exact Group.inverse.right a

theorem inverses_inv [Group α] (a: α): inverses a (-a) := by
  constructor
  exact op_inv_right a
  exact op_inv_left a

theorem op_cancel_left [Group α] {a b c: α} (h: a + b = a + c): b = c := by
  calc
    b
    _ = 0 + b        := by rw [op_unit_left]
    _ = -a + a + b   := by rw [op_inv_left]
    _ = -a + (a + b) := by rw [op_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [op_assoc]
    _ = 0 + c        := by rw [op_inv_left]
    _ = c            := by rw [op_unit_left]

theorem op_cancel_right [Group α] {a b c: α} (h: a + c = b + c): a = b := by
  calc
    a
    _ = a + 0        := by rw [op_unit_right]
    _ = a + (c + -c) := by rw [op_inv_right]
    _ = a + c + -c   := by rw [op_assoc]
    _ = b + c + -c   := by rw [h]
    _ = b + (c + -c) := by rw [op_assoc]
    _ = b + 0        := by rw [op_inv_right]
    _ = b            := by rw [op_unit_right]

theorem op_unit_inverses [Group α] {a b: α} (h: a + b = 0): -a = b := by
  have: -a + a + b = -a := by rw [op_assoc, h, op_unit_right]
  rw [←this, op_inv_left, op_unit_left]

theorem inv_unit [Group α]: -(0: α) = 0 := by
  apply op_unit_inverses
  apply op_unit_left

theorem inv_inv [Group α] (a: α): -(-a) = a := by
  apply op_cancel_right (c := -a)
  rw [op_inv_left, op_inv_right]

theorem opinv_self [Group α] (a: α): a - a = 0 := by
  apply op_inv_right

theorem inv_invop [Group α] (a b: α): -(a - b) = b - a := by
  apply op_unit_inverses
  calc
    a - b + (b - a)
    _ = a + -b + (b + -a)   := by rfl
    _ = a + (-b + (b + -a)) := by rw [op_assoc]
    _ = a + (-b + b + -a)   := by rw [op_assoc]
    _ = a + (0 + -a)        := by rw [op_inv_left]
    _ = a + -a              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_right]

-- "Socks shoes" property

theorem inv_op [Group α] (a b: α): -(a + b) = -b + -a := by
  repeat rw [←neg_eq]
  apply op_cancel_right (c := (a + b))
  rw [op_inv_left]
  apply Eq.symm
  calc
    -b + -a + (a + b)
    _ = -b + (-a + (a + b)) := by rw [op_assoc]
    _ = -b + (-a + a + b)   := by rw [op_assoc]
    _ = -b + (0 + b)        := by rw [op_inv_left]
    _ = -b + b              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_left]

-- A subgroup is a submonoid which is also closed under inverse.

class Group.sub (G: Group α) (S: Set α) extends G.toMonoid.sub S where
  inv_closed: ∀ a, a ∈ S → -a ∈ S
