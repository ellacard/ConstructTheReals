import ConstructTheReals.General.Relation

def switch (f: α → β → γ): β → α → γ :=
  λ b a ↦ f a b

variable {α: Type u} {β: Type v} {γ: Type w}

instance [LE α]: LT α := {
  lt := λ a b ↦ a ≤ b ∧ ¬ b ≤ a
}

class Bottom (α: Type u) extends LE α where
  bottom: α
  bottom_le: ∀ x, bottom ≤ x

notation "⊥" => Bottom.bottom

class Top (α: Type u) extends LE α where
  top: α
  top_ge: ∀ x, x ≤ top

notation "⊤" => Top.top

def UpperBound (R: Relation α β) (S: Set α) (b: β): Prop :=
  ∀ a, a ∈ S → R a b

def LowerBound (R: Relation α β) (S: Set β) (b: α): Prop :=
  UpperBound (switch R) S b

def UpperBounds (R: Relation α β) (S: Set α): Set β :=
  λ b ↦ UpperBound R S b

def GenLeastUpperBound (R: Relation α β) (R': Endorelation β) (S: Set α) (b: β): Prop :=
  UpperBound R S b ∧ LowerBound R' (UpperBounds R S) b

def LeastUpperBound (R: Endorelation α) (S: Set α) (b: α): Prop :=
  GenLeastUpperBound R R S b

theorem GenLeastUpperBound.unique (R: Relation α β) (R': Endorelation β) (S: Set α) (b b': β)
  (hR': Antisymmetric R') (h: GenLeastUpperBound R R' S b) (h': GenLeastUpperBound R R' S b'): b = b' := by
  apply hR'
  · exact h.right b' h'.left
  · exact h'.right b h.left

class Preorder (X: Type u) extends LE X where
  reflexive: ∀ x: X, x ≤ x
  transitive: ∀ x y z: X, x ≤ y → y ≤ z → x ≤ z

class PartialOrder (X: Type u) extends Preorder X where
  antisymmetric: ∀ x y: X, x ≤ y → y ≤ x → x = y

class Lattice (X: Type u) extends PartialOrder X, Min X, Max X where
  max_le_left: ∀ x y, x ≤ max x y
  max_le_right: ∀ x y, y ≤ max x y
  max_lub: ∀ x y z, x ≤ z → y ≤ z → max x y ≤ z
  min_le_left: ∀ x y, min x y ≤ x
  min_le_right: ∀ x y, min x y ≤ y
  min_glb: ∀ x y z, z ≤ x → z ≤ y → z ≤ min x y
