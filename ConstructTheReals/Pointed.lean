import ConstructTheReals.Function
import ConstructTheReals.Set

variable {α: Type u} {β: Type v} {γ: Type w}

class Pointed (α: Type u) where
  unit: α

export Pointed (unit)
namespace Pointed
scoped instance [Pointed α]: Zero α := ⟨unit⟩
end Pointed
open Pointed

-- A sub-pointed set is a set which contains the unit.

class Pointed.sub (P: Pointed α) (S: Set α): Prop where
  unit_mem: 0 ∈ S

theorem Pointed.sub.full (P: Pointed α): P.sub Set.full := {
  unit_mem := trivial
}
