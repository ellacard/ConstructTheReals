import ConstructTheReals.General.Set

variable {α: Type u} {β: Type v} {γ: Type w}

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

-- A submagma is a subset which is closed under the operation.

class Magma.sub (M: Magma α) (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → a + b ∈ S
