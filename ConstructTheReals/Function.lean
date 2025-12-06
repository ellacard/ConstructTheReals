variable {α: Type u} {β: Type v} {γ: Type w}

def Function.id {α: Type u}: α → α :=
  λ a ↦ a



def Function.associator (A: Type u) (B: Type v) (C: Type w): A × B × C → (A × B) × C :=
  λ ⟨a, ⟨b, c⟩⟩ ↦ ⟨⟨a, b⟩, c⟩

def Function.associator_inverse (A: Type u) (B: Type v) (C: Type w): (A × B) × C → A × B × C :=
  λ ⟨⟨a, b⟩, c⟩ ↦ ⟨a, ⟨b, c⟩⟩

def switch (f: α → β → γ): β → α → γ :=
  λ b a ↦ f a b
