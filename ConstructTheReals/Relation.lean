import ConstructTheReals.Set

variable {α: Type u} {β: Type v} {γ: Type w}

def Relation (α: Type u) (β: Type v): Type (max u v) :=
  α → β → Prop

def Endorelation (α: Type u): Type u :=
  Relation α α

def Reflexive (R: Endorelation α): Prop :=
  ∀ a, R a a

def Irreflexive (R: Endorelation α): Prop :=
  ∀ a, ¬ R a a

def Transitive (R: Endorelation α): Prop :=
  ∀ {a b c}, R a b → R b c → R a c

def Symmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a

def Antisymmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a → a = b

def Total (R: Endorelation α): Prop :=
  ∀ {a b}, R a b ∨ R b a
